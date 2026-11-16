; NOTE: Do not autogenerate
; SPDX-FileCopyrightText: 2025 Contributors to TPDE <https://tpde.org>
; SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

; RUN: tpde-lli %s | FileCheck %s

declare i32 @printf(ptr, ...)

@fmt8 = private constant [9 x i8] c"%02x %d\0A\00", align 1
define internal void @print_i8({i8, i1} %res) {
  %v = extractvalue {i8, i1} %res, 0
  %o = extractvalue {i8, i1} %res, 1
  %vx = zext i8 %v to i32
  %ox = zext i1 %o to i32
  %p = call i32 (ptr, ...) @printf(ptr @fmt8, i32 %vx, i32 %ox)
  ret void
}

@fmt16 = private constant [9 x i8] c"%04x %d\0A\00", align 1
define internal void @print_i16({i16, i1} %res) {
  %v = extractvalue {i16, i1} %res, 0
  %o = extractvalue {i16, i1} %res, 1
  %vx = zext i16 %v to i32
  %ox = zext i1 %o to i32
  %p = call i32 (ptr, ...) @printf(ptr @fmt16, i32 %vx, i32 %ox)
  ret void
}

@fmt32 = private constant [9 x i8] c"%08x %d\0A\00", align 1
define internal void @print_i32({i32, i1} %res) {
  %v = extractvalue {i32, i1} %res, 0
  %o = extractvalue {i32, i1} %res, 1
  %ox = zext i1 %o to i32
  %p = call i32 (ptr, ...) @printf(ptr @fmt32, i32 %v, i32 %ox)
  ret void
}

@fmt64 = private constant [11 x i8] c"%016lx %d\0A\00", align 1
define internal void @print_i64({i64, i1} %res) {
  %v = extractvalue {i64, i1} %res, 0
  %o = extractvalue {i64, i1} %res, 1
  %ox = zext i1 %o to i32
  %p = call i32 (ptr, ...) @printf(ptr @fmt64, i64 %v, i32 %ox)
  ret void
}

@fmt128 = private constant [17 x i8] c"%016lx%016lx %d\0A\00", align 1
define internal void @print_i128({i128, i1} %res) {
  %v = extractvalue {i128, i1} %res, 0
  %o = extractvalue {i128, i1} %res, 1
  %ox = zext i1 %o to i32
  %lo = trunc i128 %v to i64
  %hi1 = lshr i128 %v, 64
  %hi = trunc i128 %hi1 to i64
  %p = call i32 (ptr, ...) @printf(ptr @fmt128, i64 %hi, i64 %lo, i32 %ox)
  ret void
}

define i32 @main() {
; CHECK: fc 1
  %ui8_1 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0xfe, i8 u0xfe)
  call void @print_i8({i8, i1} %ui8_1)
; CHECK: fc 0
  %si8_1 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0xfe, i8 u0xfe)
  call void @print_i8({i8, i1} %si8_1)
; CHECK: fd 1
  %ui8_2 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0xfe, i8 u0xff)
  call void @print_i8({i8, i1} %ui8_2)
; CHECK: fd 0
  %si8_2 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0xfe, i8 u0xff)
  call void @print_i8({i8, i1} %si8_2)
; CHECK: fe 0
  %ui8_3 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0xfe, i8 u0x00)
  call void @print_i8({i8, i1} %ui8_3)
; CHECK: fe 0
  %si8_3 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0xfe, i8 u0x00)
  call void @print_i8({i8, i1} %si8_3)
; CHECK: ff 0
  %ui8_4 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0xfe, i8 u0x01)
  call void @print_i8({i8, i1} %ui8_4)
; CHECK: ff 0
  %si8_4 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0xfe, i8 u0x01)
  call void @print_i8({i8, i1} %si8_4)
; CHECK: 00 1
  %ui8_5 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0xfe, i8 u0x02)
  call void @print_i8({i8, i1} %ui8_5)
; CHECK: 00 0
  %si8_5 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0xfe, i8 u0x02)
  call void @print_i8({i8, i1} %si8_5)
; CHECK: 7e 1
  %ui8_6 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0xfe, i8 u0x80)
  call void @print_i8({i8, i1} %ui8_6)
; CHECK: 7e 1
  %si8_6 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0xfe, i8 u0x80)
  call void @print_i8({i8, i1} %si8_6)
; CHECK: 7d 1
  %ui8_7 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0xfe, i8 u0x7f)
  call void @print_i8({i8, i1} %ui8_7)
; CHECK: 7d 0
  %si8_7 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0xfe, i8 u0x7f)
  call void @print_i8({i8, i1} %si8_7)
; CHECK: fd 1
  %ui8_8 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0xff, i8 u0xfe)
  call void @print_i8({i8, i1} %ui8_8)
; CHECK: fd 0
  %si8_8 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0xff, i8 u0xfe)
  call void @print_i8({i8, i1} %si8_8)
; CHECK: fe 1
  %ui8_9 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0xff, i8 u0xff)
  call void @print_i8({i8, i1} %ui8_9)
; CHECK: fe 0
  %si8_9 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0xff, i8 u0xff)
  call void @print_i8({i8, i1} %si8_9)
; CHECK: ff 0
  %ui8_10 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0xff, i8 u0x00)
  call void @print_i8({i8, i1} %ui8_10)
; CHECK: ff 0
  %si8_10 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0xff, i8 u0x00)
  call void @print_i8({i8, i1} %si8_10)
; CHECK: 00 1
  %ui8_11 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0xff, i8 u0x01)
  call void @print_i8({i8, i1} %ui8_11)
; CHECK: 00 0
  %si8_11 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0xff, i8 u0x01)
  call void @print_i8({i8, i1} %si8_11)
; CHECK: 01 1
  %ui8_12 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0xff, i8 u0x02)
  call void @print_i8({i8, i1} %ui8_12)
; CHECK: 01 0
  %si8_12 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0xff, i8 u0x02)
  call void @print_i8({i8, i1} %si8_12)
; CHECK: 7f 1
  %ui8_13 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0xff, i8 u0x80)
  call void @print_i8({i8, i1} %ui8_13)
; CHECK: 7f 1
  %si8_13 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0xff, i8 u0x80)
  call void @print_i8({i8, i1} %si8_13)
; CHECK: 7e 1
  %ui8_14 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0xff, i8 u0x7f)
  call void @print_i8({i8, i1} %ui8_14)
; CHECK: 7e 0
  %si8_14 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0xff, i8 u0x7f)
  call void @print_i8({i8, i1} %si8_14)
; CHECK: fe 0
  %ui8_15 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x00, i8 u0xfe)
  call void @print_i8({i8, i1} %ui8_15)
; CHECK: fe 0
  %si8_15 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x00, i8 u0xfe)
  call void @print_i8({i8, i1} %si8_15)
; CHECK: ff 0
  %ui8_16 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x00, i8 u0xff)
  call void @print_i8({i8, i1} %ui8_16)
; CHECK: ff 0
  %si8_16 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x00, i8 u0xff)
  call void @print_i8({i8, i1} %si8_16)
; CHECK: 00 0
  %ui8_17 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x00, i8 u0x00)
  call void @print_i8({i8, i1} %ui8_17)
; CHECK: 00 0
  %si8_17 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x00, i8 u0x00)
  call void @print_i8({i8, i1} %si8_17)
; CHECK: 01 0
  %ui8_18 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x00, i8 u0x01)
  call void @print_i8({i8, i1} %ui8_18)
; CHECK: 01 0
  %si8_18 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x00, i8 u0x01)
  call void @print_i8({i8, i1} %si8_18)
; CHECK: 02 0
  %ui8_19 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x00, i8 u0x02)
  call void @print_i8({i8, i1} %ui8_19)
; CHECK: 02 0
  %si8_19 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x00, i8 u0x02)
  call void @print_i8({i8, i1} %si8_19)
; CHECK: 80 0
  %ui8_20 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x00, i8 u0x80)
  call void @print_i8({i8, i1} %ui8_20)
; CHECK: 80 0
  %si8_20 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x00, i8 u0x80)
  call void @print_i8({i8, i1} %si8_20)
; CHECK: 7f 0
  %ui8_21 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x00, i8 u0x7f)
  call void @print_i8({i8, i1} %ui8_21)
; CHECK: 7f 0
  %si8_21 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x00, i8 u0x7f)
  call void @print_i8({i8, i1} %si8_21)
; CHECK: ff 0
  %ui8_22 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x01, i8 u0xfe)
  call void @print_i8({i8, i1} %ui8_22)
; CHECK: ff 0
  %si8_22 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x01, i8 u0xfe)
  call void @print_i8({i8, i1} %si8_22)
; CHECK: 00 1
  %ui8_23 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x01, i8 u0xff)
  call void @print_i8({i8, i1} %ui8_23)
; CHECK: 00 0
  %si8_23 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x01, i8 u0xff)
  call void @print_i8({i8, i1} %si8_23)
; CHECK: 01 0
  %ui8_24 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x01, i8 u0x00)
  call void @print_i8({i8, i1} %ui8_24)
; CHECK: 01 0
  %si8_24 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x01, i8 u0x00)
  call void @print_i8({i8, i1} %si8_24)
; CHECK: 02 0
  %ui8_25 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x01, i8 u0x01)
  call void @print_i8({i8, i1} %ui8_25)
; CHECK: 02 0
  %si8_25 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x01, i8 u0x01)
  call void @print_i8({i8, i1} %si8_25)
; CHECK: 03 0
  %ui8_26 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x01, i8 u0x02)
  call void @print_i8({i8, i1} %ui8_26)
; CHECK: 03 0
  %si8_26 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x01, i8 u0x02)
  call void @print_i8({i8, i1} %si8_26)
; CHECK: 81 0
  %ui8_27 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x01, i8 u0x80)
  call void @print_i8({i8, i1} %ui8_27)
; CHECK: 81 0
  %si8_27 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x01, i8 u0x80)
  call void @print_i8({i8, i1} %si8_27)
; CHECK: 80 0
  %ui8_28 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x01, i8 u0x7f)
  call void @print_i8({i8, i1} %ui8_28)
; CHECK: 80 1
  %si8_28 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x01, i8 u0x7f)
  call void @print_i8({i8, i1} %si8_28)
; CHECK: 00 1
  %ui8_29 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x02, i8 u0xfe)
  call void @print_i8({i8, i1} %ui8_29)
; CHECK: 00 0
  %si8_29 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x02, i8 u0xfe)
  call void @print_i8({i8, i1} %si8_29)
; CHECK: 01 1
  %ui8_30 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x02, i8 u0xff)
  call void @print_i8({i8, i1} %ui8_30)
; CHECK: 01 0
  %si8_30 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x02, i8 u0xff)
  call void @print_i8({i8, i1} %si8_30)
; CHECK: 02 0
  %ui8_31 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x02, i8 u0x00)
  call void @print_i8({i8, i1} %ui8_31)
; CHECK: 02 0
  %si8_31 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x02, i8 u0x00)
  call void @print_i8({i8, i1} %si8_31)
; CHECK: 03 0
  %ui8_32 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x02, i8 u0x01)
  call void @print_i8({i8, i1} %ui8_32)
; CHECK: 03 0
  %si8_32 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x02, i8 u0x01)
  call void @print_i8({i8, i1} %si8_32)
; CHECK: 04 0
  %ui8_33 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x02, i8 u0x02)
  call void @print_i8({i8, i1} %ui8_33)
; CHECK: 04 0
  %si8_33 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x02, i8 u0x02)
  call void @print_i8({i8, i1} %si8_33)
; CHECK: 82 0
  %ui8_34 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x02, i8 u0x80)
  call void @print_i8({i8, i1} %ui8_34)
; CHECK: 82 0
  %si8_34 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x02, i8 u0x80)
  call void @print_i8({i8, i1} %si8_34)
; CHECK: 81 0
  %ui8_35 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x02, i8 u0x7f)
  call void @print_i8({i8, i1} %ui8_35)
; CHECK: 81 1
  %si8_35 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x02, i8 u0x7f)
  call void @print_i8({i8, i1} %si8_35)
; CHECK: 7e 1
  %ui8_36 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x80, i8 u0xfe)
  call void @print_i8({i8, i1} %ui8_36)
; CHECK: 7e 1
  %si8_36 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x80, i8 u0xfe)
  call void @print_i8({i8, i1} %si8_36)
; CHECK: 7f 1
  %ui8_37 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x80, i8 u0xff)
  call void @print_i8({i8, i1} %ui8_37)
; CHECK: 7f 1
  %si8_37 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x80, i8 u0xff)
  call void @print_i8({i8, i1} %si8_37)
; CHECK: 80 0
  %ui8_38 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x80, i8 u0x00)
  call void @print_i8({i8, i1} %ui8_38)
; CHECK: 80 0
  %si8_38 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x80, i8 u0x00)
  call void @print_i8({i8, i1} %si8_38)
; CHECK: 81 0
  %ui8_39 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x80, i8 u0x01)
  call void @print_i8({i8, i1} %ui8_39)
; CHECK: 81 0
  %si8_39 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x80, i8 u0x01)
  call void @print_i8({i8, i1} %si8_39)
; CHECK: 82 0
  %ui8_40 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x80, i8 u0x02)
  call void @print_i8({i8, i1} %ui8_40)
; CHECK: 82 0
  %si8_40 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x80, i8 u0x02)
  call void @print_i8({i8, i1} %si8_40)
; CHECK: 00 1
  %ui8_41 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x80, i8 u0x80)
  call void @print_i8({i8, i1} %ui8_41)
; CHECK: 00 1
  %si8_41 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x80, i8 u0x80)
  call void @print_i8({i8, i1} %si8_41)
; CHECK: ff 0
  %ui8_42 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x80, i8 u0x7f)
  call void @print_i8({i8, i1} %ui8_42)
; CHECK: ff 0
  %si8_42 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x80, i8 u0x7f)
  call void @print_i8({i8, i1} %si8_42)
; CHECK: 7d 1
  %ui8_43 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x7f, i8 u0xfe)
  call void @print_i8({i8, i1} %ui8_43)
; CHECK: 7d 0
  %si8_43 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x7f, i8 u0xfe)
  call void @print_i8({i8, i1} %si8_43)
; CHECK: 7e 1
  %ui8_44 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x7f, i8 u0xff)
  call void @print_i8({i8, i1} %ui8_44)
; CHECK: 7e 0
  %si8_44 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x7f, i8 u0xff)
  call void @print_i8({i8, i1} %si8_44)
; CHECK: 7f 0
  %ui8_45 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x7f, i8 u0x00)
  call void @print_i8({i8, i1} %ui8_45)
; CHECK: 7f 0
  %si8_45 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x7f, i8 u0x00)
  call void @print_i8({i8, i1} %si8_45)
; CHECK: 80 0
  %ui8_46 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x7f, i8 u0x01)
  call void @print_i8({i8, i1} %ui8_46)
; CHECK: 80 1
  %si8_46 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x7f, i8 u0x01)
  call void @print_i8({i8, i1} %si8_46)
; CHECK: 81 0
  %ui8_47 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x7f, i8 u0x02)
  call void @print_i8({i8, i1} %ui8_47)
; CHECK: 81 1
  %si8_47 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x7f, i8 u0x02)
  call void @print_i8({i8, i1} %si8_47)
; CHECK: ff 0
  %ui8_48 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x7f, i8 u0x80)
  call void @print_i8({i8, i1} %ui8_48)
; CHECK: ff 0
  %si8_48 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x7f, i8 u0x80)
  call void @print_i8({i8, i1} %si8_48)
; CHECK: fe 0
  %ui8_49 = call {i8, i1} @llvm.uadd.with.overflow(i8 u0x7f, i8 u0x7f)
  call void @print_i8({i8, i1} %ui8_49)
; CHECK: fe 1
  %si8_49 = call {i8, i1} @llvm.sadd.with.overflow(i8 u0x7f, i8 u0x7f)
  call void @print_i8({i8, i1} %si8_49)

; CHECK: fffc 1
  %ui16_1 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0xfffe, i16 u0xfffe)
  call void @print_i16({i16, i1} %ui16_1)
; CHECK: fffc 0
  %si16_1 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0xfffe, i16 u0xfffe)
  call void @print_i16({i16, i1} %si16_1)
; CHECK: fffd 1
  %ui16_2 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0xfffe, i16 u0xffff)
  call void @print_i16({i16, i1} %ui16_2)
; CHECK: fffd 0
  %si16_2 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0xfffe, i16 u0xffff)
  call void @print_i16({i16, i1} %si16_2)
; CHECK: fffe 0
  %ui16_3 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0xfffe, i16 u0x0000)
  call void @print_i16({i16, i1} %ui16_3)
; CHECK: fffe 0
  %si16_3 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0xfffe, i16 u0x0000)
  call void @print_i16({i16, i1} %si16_3)
; CHECK: ffff 0
  %ui16_4 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0xfffe, i16 u0x0001)
  call void @print_i16({i16, i1} %ui16_4)
; CHECK: ffff 0
  %si16_4 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0xfffe, i16 u0x0001)
  call void @print_i16({i16, i1} %si16_4)
; CHECK: 0000 1
  %ui16_5 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0xfffe, i16 u0x0002)
  call void @print_i16({i16, i1} %ui16_5)
; CHECK: 0000 0
  %si16_5 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0xfffe, i16 u0x0002)
  call void @print_i16({i16, i1} %si16_5)
; CHECK: 7ffe 1
  %ui16_6 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0xfffe, i16 u0x8000)
  call void @print_i16({i16, i1} %ui16_6)
; CHECK: 7ffe 1
  %si16_6 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0xfffe, i16 u0x8000)
  call void @print_i16({i16, i1} %si16_6)
; CHECK: 7ffd 1
  %ui16_7 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0xfffe, i16 u0x7fff)
  call void @print_i16({i16, i1} %ui16_7)
; CHECK: 7ffd 0
  %si16_7 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0xfffe, i16 u0x7fff)
  call void @print_i16({i16, i1} %si16_7)
; CHECK: fffd 1
  %ui16_8 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0xffff, i16 u0xfffe)
  call void @print_i16({i16, i1} %ui16_8)
; CHECK: fffd 0
  %si16_8 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0xffff, i16 u0xfffe)
  call void @print_i16({i16, i1} %si16_8)
; CHECK: fffe 1
  %ui16_9 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0xffff, i16 u0xffff)
  call void @print_i16({i16, i1} %ui16_9)
; CHECK: fffe 0
  %si16_9 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0xffff, i16 u0xffff)
  call void @print_i16({i16, i1} %si16_9)
; CHECK: ffff 0
  %ui16_10 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0xffff, i16 u0x0000)
  call void @print_i16({i16, i1} %ui16_10)
; CHECK: ffff 0
  %si16_10 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0xffff, i16 u0x0000)
  call void @print_i16({i16, i1} %si16_10)
; CHECK: 0000 1
  %ui16_11 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0xffff, i16 u0x0001)
  call void @print_i16({i16, i1} %ui16_11)
; CHECK: 0000 0
  %si16_11 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0xffff, i16 u0x0001)
  call void @print_i16({i16, i1} %si16_11)
; CHECK: 0001 1
  %ui16_12 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0xffff, i16 u0x0002)
  call void @print_i16({i16, i1} %ui16_12)
; CHECK: 0001 0
  %si16_12 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0xffff, i16 u0x0002)
  call void @print_i16({i16, i1} %si16_12)
; CHECK: 7fff 1
  %ui16_13 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0xffff, i16 u0x8000)
  call void @print_i16({i16, i1} %ui16_13)
; CHECK: 7fff 1
  %si16_13 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0xffff, i16 u0x8000)
  call void @print_i16({i16, i1} %si16_13)
; CHECK: 7ffe 1
  %ui16_14 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0xffff, i16 u0x7fff)
  call void @print_i16({i16, i1} %ui16_14)
; CHECK: 7ffe 0
  %si16_14 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0xffff, i16 u0x7fff)
  call void @print_i16({i16, i1} %si16_14)
; CHECK: fffe 0
  %ui16_15 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x0000, i16 u0xfffe)
  call void @print_i16({i16, i1} %ui16_15)
; CHECK: fffe 0
  %si16_15 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x0000, i16 u0xfffe)
  call void @print_i16({i16, i1} %si16_15)
; CHECK: ffff 0
  %ui16_16 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x0000, i16 u0xffff)
  call void @print_i16({i16, i1} %ui16_16)
; CHECK: ffff 0
  %si16_16 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x0000, i16 u0xffff)
  call void @print_i16({i16, i1} %si16_16)
; CHECK: 0000 0
  %ui16_17 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x0000, i16 u0x0000)
  call void @print_i16({i16, i1} %ui16_17)
; CHECK: 0000 0
  %si16_17 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x0000, i16 u0x0000)
  call void @print_i16({i16, i1} %si16_17)
; CHECK: 0001 0
  %ui16_18 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x0000, i16 u0x0001)
  call void @print_i16({i16, i1} %ui16_18)
; CHECK: 0001 0
  %si16_18 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x0000, i16 u0x0001)
  call void @print_i16({i16, i1} %si16_18)
; CHECK: 0002 0
  %ui16_19 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x0000, i16 u0x0002)
  call void @print_i16({i16, i1} %ui16_19)
; CHECK: 0002 0
  %si16_19 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x0000, i16 u0x0002)
  call void @print_i16({i16, i1} %si16_19)
; CHECK: 8000 0
  %ui16_20 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x0000, i16 u0x8000)
  call void @print_i16({i16, i1} %ui16_20)
; CHECK: 8000 0
  %si16_20 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x0000, i16 u0x8000)
  call void @print_i16({i16, i1} %si16_20)
; CHECK: 7fff 0
  %ui16_21 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x0000, i16 u0x7fff)
  call void @print_i16({i16, i1} %ui16_21)
; CHECK: 7fff 0
  %si16_21 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x0000, i16 u0x7fff)
  call void @print_i16({i16, i1} %si16_21)
; CHECK: ffff 0
  %ui16_22 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x0001, i16 u0xfffe)
  call void @print_i16({i16, i1} %ui16_22)
; CHECK: ffff 0
  %si16_22 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x0001, i16 u0xfffe)
  call void @print_i16({i16, i1} %si16_22)
; CHECK: 0000 1
  %ui16_23 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x0001, i16 u0xffff)
  call void @print_i16({i16, i1} %ui16_23)
; CHECK: 0000 0
  %si16_23 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x0001, i16 u0xffff)
  call void @print_i16({i16, i1} %si16_23)
; CHECK: 0001 0
  %ui16_24 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x0001, i16 u0x0000)
  call void @print_i16({i16, i1} %ui16_24)
; CHECK: 0001 0
  %si16_24 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x0001, i16 u0x0000)
  call void @print_i16({i16, i1} %si16_24)
; CHECK: 0002 0
  %ui16_25 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x0001, i16 u0x0001)
  call void @print_i16({i16, i1} %ui16_25)
; CHECK: 0002 0
  %si16_25 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x0001, i16 u0x0001)
  call void @print_i16({i16, i1} %si16_25)
; CHECK: 0003 0
  %ui16_26 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x0001, i16 u0x0002)
  call void @print_i16({i16, i1} %ui16_26)
; CHECK: 0003 0
  %si16_26 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x0001, i16 u0x0002)
  call void @print_i16({i16, i1} %si16_26)
; CHECK: 8001 0
  %ui16_27 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x0001, i16 u0x8000)
  call void @print_i16({i16, i1} %ui16_27)
; CHECK: 8001 0
  %si16_27 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x0001, i16 u0x8000)
  call void @print_i16({i16, i1} %si16_27)
; CHECK: 8000 0
  %ui16_28 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x0001, i16 u0x7fff)
  call void @print_i16({i16, i1} %ui16_28)
; CHECK: 8000 1
  %si16_28 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x0001, i16 u0x7fff)
  call void @print_i16({i16, i1} %si16_28)
; CHECK: 0000 1
  %ui16_29 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x0002, i16 u0xfffe)
  call void @print_i16({i16, i1} %ui16_29)
; CHECK: 0000 0
  %si16_29 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x0002, i16 u0xfffe)
  call void @print_i16({i16, i1} %si16_29)
; CHECK: 0001 1
  %ui16_30 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x0002, i16 u0xffff)
  call void @print_i16({i16, i1} %ui16_30)
; CHECK: 0001 0
  %si16_30 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x0002, i16 u0xffff)
  call void @print_i16({i16, i1} %si16_30)
; CHECK: 0002 0
  %ui16_31 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x0002, i16 u0x0000)
  call void @print_i16({i16, i1} %ui16_31)
; CHECK: 0002 0
  %si16_31 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x0002, i16 u0x0000)
  call void @print_i16({i16, i1} %si16_31)
; CHECK: 0003 0
  %ui16_32 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x0002, i16 u0x0001)
  call void @print_i16({i16, i1} %ui16_32)
; CHECK: 0003 0
  %si16_32 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x0002, i16 u0x0001)
  call void @print_i16({i16, i1} %si16_32)
; CHECK: 0004 0
  %ui16_33 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x0002, i16 u0x0002)
  call void @print_i16({i16, i1} %ui16_33)
; CHECK: 0004 0
  %si16_33 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x0002, i16 u0x0002)
  call void @print_i16({i16, i1} %si16_33)
; CHECK: 8002 0
  %ui16_34 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x0002, i16 u0x8000)
  call void @print_i16({i16, i1} %ui16_34)
; CHECK: 8002 0
  %si16_34 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x0002, i16 u0x8000)
  call void @print_i16({i16, i1} %si16_34)
; CHECK: 8001 0
  %ui16_35 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x0002, i16 u0x7fff)
  call void @print_i16({i16, i1} %ui16_35)
; CHECK: 8001 1
  %si16_35 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x0002, i16 u0x7fff)
  call void @print_i16({i16, i1} %si16_35)
; CHECK: 7ffe 1
  %ui16_36 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x8000, i16 u0xfffe)
  call void @print_i16({i16, i1} %ui16_36)
; CHECK: 7ffe 1
  %si16_36 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x8000, i16 u0xfffe)
  call void @print_i16({i16, i1} %si16_36)
; CHECK: 7fff 1
  %ui16_37 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x8000, i16 u0xffff)
  call void @print_i16({i16, i1} %ui16_37)
; CHECK: 7fff 1
  %si16_37 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x8000, i16 u0xffff)
  call void @print_i16({i16, i1} %si16_37)
; CHECK: 8000 0
  %ui16_38 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x8000, i16 u0x0000)
  call void @print_i16({i16, i1} %ui16_38)
; CHECK: 8000 0
  %si16_38 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x8000, i16 u0x0000)
  call void @print_i16({i16, i1} %si16_38)
; CHECK: 8001 0
  %ui16_39 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x8000, i16 u0x0001)
  call void @print_i16({i16, i1} %ui16_39)
; CHECK: 8001 0
  %si16_39 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x8000, i16 u0x0001)
  call void @print_i16({i16, i1} %si16_39)
; CHECK: 8002 0
  %ui16_40 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x8000, i16 u0x0002)
  call void @print_i16({i16, i1} %ui16_40)
; CHECK: 8002 0
  %si16_40 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x8000, i16 u0x0002)
  call void @print_i16({i16, i1} %si16_40)
; CHECK: 0000 1
  %ui16_41 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x8000, i16 u0x8000)
  call void @print_i16({i16, i1} %ui16_41)
; CHECK: 0000 1
  %si16_41 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x8000, i16 u0x8000)
  call void @print_i16({i16, i1} %si16_41)
; CHECK: ffff 0
  %ui16_42 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x8000, i16 u0x7fff)
  call void @print_i16({i16, i1} %ui16_42)
; CHECK: ffff 0
  %si16_42 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x8000, i16 u0x7fff)
  call void @print_i16({i16, i1} %si16_42)
; CHECK: 7ffd 1
  %ui16_43 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x7fff, i16 u0xfffe)
  call void @print_i16({i16, i1} %ui16_43)
; CHECK: 7ffd 0
  %si16_43 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x7fff, i16 u0xfffe)
  call void @print_i16({i16, i1} %si16_43)
; CHECK: 7ffe 1
  %ui16_44 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x7fff, i16 u0xffff)
  call void @print_i16({i16, i1} %ui16_44)
; CHECK: 7ffe 0
  %si16_44 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x7fff, i16 u0xffff)
  call void @print_i16({i16, i1} %si16_44)
; CHECK: 7fff 0
  %ui16_45 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x7fff, i16 u0x0000)
  call void @print_i16({i16, i1} %ui16_45)
; CHECK: 7fff 0
  %si16_45 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x7fff, i16 u0x0000)
  call void @print_i16({i16, i1} %si16_45)
; CHECK: 8000 0
  %ui16_46 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x7fff, i16 u0x0001)
  call void @print_i16({i16, i1} %ui16_46)
; CHECK: 8000 1
  %si16_46 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x7fff, i16 u0x0001)
  call void @print_i16({i16, i1} %si16_46)
; CHECK: 8001 0
  %ui16_47 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x7fff, i16 u0x0002)
  call void @print_i16({i16, i1} %ui16_47)
; CHECK: 8001 1
  %si16_47 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x7fff, i16 u0x0002)
  call void @print_i16({i16, i1} %si16_47)
; CHECK: ffff 0
  %ui16_48 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x7fff, i16 u0x8000)
  call void @print_i16({i16, i1} %ui16_48)
; CHECK: ffff 0
  %si16_48 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x7fff, i16 u0x8000)
  call void @print_i16({i16, i1} %si16_48)
; CHECK: fffe 0
  %ui16_49 = call {i16, i1} @llvm.uadd.with.overflow(i16 u0x7fff, i16 u0x7fff)
  call void @print_i16({i16, i1} %ui16_49)
; CHECK: fffe 1
  %si16_49 = call {i16, i1} @llvm.sadd.with.overflow(i16 u0x7fff, i16 u0x7fff)
  call void @print_i16({i16, i1} %si16_49)

; CHECK: fffffffc 1
  %ui32_1 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0xfffffffe, i32 u0xfffffffe)
  call void @print_i32({i32, i1} %ui32_1)
; CHECK: fffffffc 0
  %si32_1 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0xfffffffe, i32 u0xfffffffe)
  call void @print_i32({i32, i1} %si32_1)
; CHECK: fffffffd 1
  %ui32_2 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0xfffffffe, i32 u0xffffffff)
  call void @print_i32({i32, i1} %ui32_2)
; CHECK: fffffffd 0
  %si32_2 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0xfffffffe, i32 u0xffffffff)
  call void @print_i32({i32, i1} %si32_2)
; CHECK: fffffffe 0
  %ui32_3 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0xfffffffe, i32 u0x00000000)
  call void @print_i32({i32, i1} %ui32_3)
; CHECK: fffffffe 0
  %si32_3 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0xfffffffe, i32 u0x00000000)
  call void @print_i32({i32, i1} %si32_3)
; CHECK: ffffffff 0
  %ui32_4 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0xfffffffe, i32 u0x00000001)
  call void @print_i32({i32, i1} %ui32_4)
; CHECK: ffffffff 0
  %si32_4 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0xfffffffe, i32 u0x00000001)
  call void @print_i32({i32, i1} %si32_4)
; CHECK: 00000000 1
  %ui32_5 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0xfffffffe, i32 u0x00000002)
  call void @print_i32({i32, i1} %ui32_5)
; CHECK: 00000000 0
  %si32_5 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0xfffffffe, i32 u0x00000002)
  call void @print_i32({i32, i1} %si32_5)
; CHECK: 7ffffffe 1
  %ui32_6 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0xfffffffe, i32 u0x80000000)
  call void @print_i32({i32, i1} %ui32_6)
; CHECK: 7ffffffe 1
  %si32_6 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0xfffffffe, i32 u0x80000000)
  call void @print_i32({i32, i1} %si32_6)
; CHECK: 7ffffffd 1
  %ui32_7 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0xfffffffe, i32 u0x7fffffff)
  call void @print_i32({i32, i1} %ui32_7)
; CHECK: 7ffffffd 0
  %si32_7 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0xfffffffe, i32 u0x7fffffff)
  call void @print_i32({i32, i1} %si32_7)
; CHECK: fffffffd 1
  %ui32_8 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0xffffffff, i32 u0xfffffffe)
  call void @print_i32({i32, i1} %ui32_8)
; CHECK: fffffffd 0
  %si32_8 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0xffffffff, i32 u0xfffffffe)
  call void @print_i32({i32, i1} %si32_8)
; CHECK: fffffffe 1
  %ui32_9 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0xffffffff, i32 u0xffffffff)
  call void @print_i32({i32, i1} %ui32_9)
; CHECK: fffffffe 0
  %si32_9 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0xffffffff, i32 u0xffffffff)
  call void @print_i32({i32, i1} %si32_9)
; CHECK: ffffffff 0
  %ui32_10 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0xffffffff, i32 u0x00000000)
  call void @print_i32({i32, i1} %ui32_10)
; CHECK: ffffffff 0
  %si32_10 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0xffffffff, i32 u0x00000000)
  call void @print_i32({i32, i1} %si32_10)
; CHECK: 00000000 1
  %ui32_11 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0xffffffff, i32 u0x00000001)
  call void @print_i32({i32, i1} %ui32_11)
; CHECK: 00000000 0
  %si32_11 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0xffffffff, i32 u0x00000001)
  call void @print_i32({i32, i1} %si32_11)
; CHECK: 00000001 1
  %ui32_12 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0xffffffff, i32 u0x00000002)
  call void @print_i32({i32, i1} %ui32_12)
; CHECK: 00000001 0
  %si32_12 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0xffffffff, i32 u0x00000002)
  call void @print_i32({i32, i1} %si32_12)
; CHECK: 7fffffff 1
  %ui32_13 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0xffffffff, i32 u0x80000000)
  call void @print_i32({i32, i1} %ui32_13)
; CHECK: 7fffffff 1
  %si32_13 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0xffffffff, i32 u0x80000000)
  call void @print_i32({i32, i1} %si32_13)
; CHECK: 7ffffffe 1
  %ui32_14 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0xffffffff, i32 u0x7fffffff)
  call void @print_i32({i32, i1} %ui32_14)
; CHECK: 7ffffffe 0
  %si32_14 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0xffffffff, i32 u0x7fffffff)
  call void @print_i32({i32, i1} %si32_14)
; CHECK: fffffffe 0
  %ui32_15 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x00000000, i32 u0xfffffffe)
  call void @print_i32({i32, i1} %ui32_15)
; CHECK: fffffffe 0
  %si32_15 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x00000000, i32 u0xfffffffe)
  call void @print_i32({i32, i1} %si32_15)
; CHECK: ffffffff 0
  %ui32_16 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x00000000, i32 u0xffffffff)
  call void @print_i32({i32, i1} %ui32_16)
; CHECK: ffffffff 0
  %si32_16 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x00000000, i32 u0xffffffff)
  call void @print_i32({i32, i1} %si32_16)
; CHECK: 00000000 0
  %ui32_17 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x00000000, i32 u0x00000000)
  call void @print_i32({i32, i1} %ui32_17)
; CHECK: 00000000 0
  %si32_17 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x00000000, i32 u0x00000000)
  call void @print_i32({i32, i1} %si32_17)
; CHECK: 00000001 0
  %ui32_18 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x00000000, i32 u0x00000001)
  call void @print_i32({i32, i1} %ui32_18)
; CHECK: 00000001 0
  %si32_18 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x00000000, i32 u0x00000001)
  call void @print_i32({i32, i1} %si32_18)
; CHECK: 00000002 0
  %ui32_19 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x00000000, i32 u0x00000002)
  call void @print_i32({i32, i1} %ui32_19)
; CHECK: 00000002 0
  %si32_19 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x00000000, i32 u0x00000002)
  call void @print_i32({i32, i1} %si32_19)
; CHECK: 80000000 0
  %ui32_20 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x00000000, i32 u0x80000000)
  call void @print_i32({i32, i1} %ui32_20)
; CHECK: 80000000 0
  %si32_20 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x00000000, i32 u0x80000000)
  call void @print_i32({i32, i1} %si32_20)
; CHECK: 7fffffff 0
  %ui32_21 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x00000000, i32 u0x7fffffff)
  call void @print_i32({i32, i1} %ui32_21)
; CHECK: 7fffffff 0
  %si32_21 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x00000000, i32 u0x7fffffff)
  call void @print_i32({i32, i1} %si32_21)
; CHECK: ffffffff 0
  %ui32_22 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x00000001, i32 u0xfffffffe)
  call void @print_i32({i32, i1} %ui32_22)
; CHECK: ffffffff 0
  %si32_22 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x00000001, i32 u0xfffffffe)
  call void @print_i32({i32, i1} %si32_22)
; CHECK: 00000000 1
  %ui32_23 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x00000001, i32 u0xffffffff)
  call void @print_i32({i32, i1} %ui32_23)
; CHECK: 00000000 0
  %si32_23 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x00000001, i32 u0xffffffff)
  call void @print_i32({i32, i1} %si32_23)
; CHECK: 00000001 0
  %ui32_24 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x00000001, i32 u0x00000000)
  call void @print_i32({i32, i1} %ui32_24)
; CHECK: 00000001 0
  %si32_24 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x00000001, i32 u0x00000000)
  call void @print_i32({i32, i1} %si32_24)
; CHECK: 00000002 0
  %ui32_25 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x00000001, i32 u0x00000001)
  call void @print_i32({i32, i1} %ui32_25)
; CHECK: 00000002 0
  %si32_25 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x00000001, i32 u0x00000001)
  call void @print_i32({i32, i1} %si32_25)
; CHECK: 00000003 0
  %ui32_26 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x00000001, i32 u0x00000002)
  call void @print_i32({i32, i1} %ui32_26)
; CHECK: 00000003 0
  %si32_26 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x00000001, i32 u0x00000002)
  call void @print_i32({i32, i1} %si32_26)
; CHECK: 80000001 0
  %ui32_27 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x00000001, i32 u0x80000000)
  call void @print_i32({i32, i1} %ui32_27)
; CHECK: 80000001 0
  %si32_27 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x00000001, i32 u0x80000000)
  call void @print_i32({i32, i1} %si32_27)
; CHECK: 80000000 0
  %ui32_28 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x00000001, i32 u0x7fffffff)
  call void @print_i32({i32, i1} %ui32_28)
; CHECK: 80000000 1
  %si32_28 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x00000001, i32 u0x7fffffff)
  call void @print_i32({i32, i1} %si32_28)
; CHECK: 00000000 1
  %ui32_29 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x00000002, i32 u0xfffffffe)
  call void @print_i32({i32, i1} %ui32_29)
; CHECK: 00000000 0
  %si32_29 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x00000002, i32 u0xfffffffe)
  call void @print_i32({i32, i1} %si32_29)
; CHECK: 00000001 1
  %ui32_30 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x00000002, i32 u0xffffffff)
  call void @print_i32({i32, i1} %ui32_30)
; CHECK: 00000001 0
  %si32_30 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x00000002, i32 u0xffffffff)
  call void @print_i32({i32, i1} %si32_30)
; CHECK: 00000002 0
  %ui32_31 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x00000002, i32 u0x00000000)
  call void @print_i32({i32, i1} %ui32_31)
; CHECK: 00000002 0
  %si32_31 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x00000002, i32 u0x00000000)
  call void @print_i32({i32, i1} %si32_31)
; CHECK: 00000003 0
  %ui32_32 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x00000002, i32 u0x00000001)
  call void @print_i32({i32, i1} %ui32_32)
; CHECK: 00000003 0
  %si32_32 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x00000002, i32 u0x00000001)
  call void @print_i32({i32, i1} %si32_32)
; CHECK: 00000004 0
  %ui32_33 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x00000002, i32 u0x00000002)
  call void @print_i32({i32, i1} %ui32_33)
; CHECK: 00000004 0
  %si32_33 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x00000002, i32 u0x00000002)
  call void @print_i32({i32, i1} %si32_33)
; CHECK: 80000002 0
  %ui32_34 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x00000002, i32 u0x80000000)
  call void @print_i32({i32, i1} %ui32_34)
; CHECK: 80000002 0
  %si32_34 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x00000002, i32 u0x80000000)
  call void @print_i32({i32, i1} %si32_34)
; CHECK: 80000001 0
  %ui32_35 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x00000002, i32 u0x7fffffff)
  call void @print_i32({i32, i1} %ui32_35)
; CHECK: 80000001 1
  %si32_35 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x00000002, i32 u0x7fffffff)
  call void @print_i32({i32, i1} %si32_35)
; CHECK: 7ffffffe 1
  %ui32_36 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x80000000, i32 u0xfffffffe)
  call void @print_i32({i32, i1} %ui32_36)
; CHECK: 7ffffffe 1
  %si32_36 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x80000000, i32 u0xfffffffe)
  call void @print_i32({i32, i1} %si32_36)
; CHECK: 7fffffff 1
  %ui32_37 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x80000000, i32 u0xffffffff)
  call void @print_i32({i32, i1} %ui32_37)
; CHECK: 7fffffff 1
  %si32_37 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x80000000, i32 u0xffffffff)
  call void @print_i32({i32, i1} %si32_37)
; CHECK: 80000000 0
  %ui32_38 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x80000000, i32 u0x00000000)
  call void @print_i32({i32, i1} %ui32_38)
; CHECK: 80000000 0
  %si32_38 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x80000000, i32 u0x00000000)
  call void @print_i32({i32, i1} %si32_38)
; CHECK: 80000001 0
  %ui32_39 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x80000000, i32 u0x00000001)
  call void @print_i32({i32, i1} %ui32_39)
; CHECK: 80000001 0
  %si32_39 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x80000000, i32 u0x00000001)
  call void @print_i32({i32, i1} %si32_39)
; CHECK: 80000002 0
  %ui32_40 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x80000000, i32 u0x00000002)
  call void @print_i32({i32, i1} %ui32_40)
; CHECK: 80000002 0
  %si32_40 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x80000000, i32 u0x00000002)
  call void @print_i32({i32, i1} %si32_40)
; CHECK: 00000000 1
  %ui32_41 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x80000000, i32 u0x80000000)
  call void @print_i32({i32, i1} %ui32_41)
; CHECK: 00000000 1
  %si32_41 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x80000000, i32 u0x80000000)
  call void @print_i32({i32, i1} %si32_41)
; CHECK: ffffffff 0
  %ui32_42 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x80000000, i32 u0x7fffffff)
  call void @print_i32({i32, i1} %ui32_42)
; CHECK: ffffffff 0
  %si32_42 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x80000000, i32 u0x7fffffff)
  call void @print_i32({i32, i1} %si32_42)
; CHECK: 7ffffffd 1
  %ui32_43 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x7fffffff, i32 u0xfffffffe)
  call void @print_i32({i32, i1} %ui32_43)
; CHECK: 7ffffffd 0
  %si32_43 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x7fffffff, i32 u0xfffffffe)
  call void @print_i32({i32, i1} %si32_43)
; CHECK: 7ffffffe 1
  %ui32_44 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x7fffffff, i32 u0xffffffff)
  call void @print_i32({i32, i1} %ui32_44)
; CHECK: 7ffffffe 0
  %si32_44 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x7fffffff, i32 u0xffffffff)
  call void @print_i32({i32, i1} %si32_44)
; CHECK: 7fffffff 0
  %ui32_45 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x7fffffff, i32 u0x00000000)
  call void @print_i32({i32, i1} %ui32_45)
; CHECK: 7fffffff 0
  %si32_45 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x7fffffff, i32 u0x00000000)
  call void @print_i32({i32, i1} %si32_45)
; CHECK: 80000000 0
  %ui32_46 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x7fffffff, i32 u0x00000001)
  call void @print_i32({i32, i1} %ui32_46)
; CHECK: 80000000 1
  %si32_46 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x7fffffff, i32 u0x00000001)
  call void @print_i32({i32, i1} %si32_46)
; CHECK: 80000001 0
  %ui32_47 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x7fffffff, i32 u0x00000002)
  call void @print_i32({i32, i1} %ui32_47)
; CHECK: 80000001 1
  %si32_47 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x7fffffff, i32 u0x00000002)
  call void @print_i32({i32, i1} %si32_47)
; CHECK: ffffffff 0
  %ui32_48 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x7fffffff, i32 u0x80000000)
  call void @print_i32({i32, i1} %ui32_48)
; CHECK: ffffffff 0
  %si32_48 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x7fffffff, i32 u0x80000000)
  call void @print_i32({i32, i1} %si32_48)
; CHECK: fffffffe 0
  %ui32_49 = call {i32, i1} @llvm.uadd.with.overflow(i32 u0x7fffffff, i32 u0x7fffffff)
  call void @print_i32({i32, i1} %ui32_49)
; CHECK: fffffffe 1
  %si32_49 = call {i32, i1} @llvm.sadd.with.overflow(i32 u0x7fffffff, i32 u0x7fffffff)
  call void @print_i32({i32, i1} %si32_49)

; CHECK: fffffffffffffffc 1
  %ui64_1 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0xfffffffffffffffe, i64 u0xfffffffffffffffe)
  call void @print_i64({i64, i1} %ui64_1)
; CHECK: fffffffffffffffc 0
  %si64_1 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0xfffffffffffffffe, i64 u0xfffffffffffffffe)
  call void @print_i64({i64, i1} %si64_1)
; CHECK: fffffffffffffffd 1
  %ui64_2 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0xfffffffffffffffe, i64 u0xffffffffffffffff)
  call void @print_i64({i64, i1} %ui64_2)
; CHECK: fffffffffffffffd 0
  %si64_2 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0xfffffffffffffffe, i64 u0xffffffffffffffff)
  call void @print_i64({i64, i1} %si64_2)
; CHECK: fffffffffffffffe 0
  %ui64_3 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0xfffffffffffffffe, i64 u0x0000000000000000)
  call void @print_i64({i64, i1} %ui64_3)
; CHECK: fffffffffffffffe 0
  %si64_3 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0xfffffffffffffffe, i64 u0x0000000000000000)
  call void @print_i64({i64, i1} %si64_3)
; CHECK: ffffffffffffffff 0
  %ui64_4 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0xfffffffffffffffe, i64 u0x0000000000000001)
  call void @print_i64({i64, i1} %ui64_4)
; CHECK: ffffffffffffffff 0
  %si64_4 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0xfffffffffffffffe, i64 u0x0000000000000001)
  call void @print_i64({i64, i1} %si64_4)
; CHECK: 0000000000000000 1
  %ui64_5 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0xfffffffffffffffe, i64 u0x0000000000000002)
  call void @print_i64({i64, i1} %ui64_5)
; CHECK: 0000000000000000 0
  %si64_5 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0xfffffffffffffffe, i64 u0x0000000000000002)
  call void @print_i64({i64, i1} %si64_5)
; CHECK: 7ffffffffffffffe 1
  %ui64_6 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0xfffffffffffffffe, i64 u0x8000000000000000)
  call void @print_i64({i64, i1} %ui64_6)
; CHECK: 7ffffffffffffffe 1
  %si64_6 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0xfffffffffffffffe, i64 u0x8000000000000000)
  call void @print_i64({i64, i1} %si64_6)
; CHECK: 7ffffffffffffffd 1
  %ui64_7 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0xfffffffffffffffe, i64 u0x7fffffffffffffff)
  call void @print_i64({i64, i1} %ui64_7)
; CHECK: 7ffffffffffffffd 0
  %si64_7 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0xfffffffffffffffe, i64 u0x7fffffffffffffff)
  call void @print_i64({i64, i1} %si64_7)
; CHECK: fffffffffffffffd 1
  %ui64_8 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0xffffffffffffffff, i64 u0xfffffffffffffffe)
  call void @print_i64({i64, i1} %ui64_8)
; CHECK: fffffffffffffffd 0
  %si64_8 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0xffffffffffffffff, i64 u0xfffffffffffffffe)
  call void @print_i64({i64, i1} %si64_8)
; CHECK: fffffffffffffffe 1
  %ui64_9 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0xffffffffffffffff, i64 u0xffffffffffffffff)
  call void @print_i64({i64, i1} %ui64_9)
; CHECK: fffffffffffffffe 0
  %si64_9 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0xffffffffffffffff, i64 u0xffffffffffffffff)
  call void @print_i64({i64, i1} %si64_9)
; CHECK: ffffffffffffffff 0
  %ui64_10 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0xffffffffffffffff, i64 u0x0000000000000000)
  call void @print_i64({i64, i1} %ui64_10)
; CHECK: ffffffffffffffff 0
  %si64_10 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0xffffffffffffffff, i64 u0x0000000000000000)
  call void @print_i64({i64, i1} %si64_10)
; CHECK: 0000000000000000 1
  %ui64_11 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0xffffffffffffffff, i64 u0x0000000000000001)
  call void @print_i64({i64, i1} %ui64_11)
; CHECK: 0000000000000000 0
  %si64_11 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0xffffffffffffffff, i64 u0x0000000000000001)
  call void @print_i64({i64, i1} %si64_11)
; CHECK: 0000000000000001 1
  %ui64_12 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0xffffffffffffffff, i64 u0x0000000000000002)
  call void @print_i64({i64, i1} %ui64_12)
; CHECK: 0000000000000001 0
  %si64_12 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0xffffffffffffffff, i64 u0x0000000000000002)
  call void @print_i64({i64, i1} %si64_12)
; CHECK: 7fffffffffffffff 1
  %ui64_13 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0xffffffffffffffff, i64 u0x8000000000000000)
  call void @print_i64({i64, i1} %ui64_13)
; CHECK: 7fffffffffffffff 1
  %si64_13 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0xffffffffffffffff, i64 u0x8000000000000000)
  call void @print_i64({i64, i1} %si64_13)
; CHECK: 7ffffffffffffffe 1
  %ui64_14 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0xffffffffffffffff, i64 u0x7fffffffffffffff)
  call void @print_i64({i64, i1} %ui64_14)
; CHECK: 7ffffffffffffffe 0
  %si64_14 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0xffffffffffffffff, i64 u0x7fffffffffffffff)
  call void @print_i64({i64, i1} %si64_14)
; CHECK: fffffffffffffffe 0
  %ui64_15 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x0000000000000000, i64 u0xfffffffffffffffe)
  call void @print_i64({i64, i1} %ui64_15)
; CHECK: fffffffffffffffe 0
  %si64_15 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x0000000000000000, i64 u0xfffffffffffffffe)
  call void @print_i64({i64, i1} %si64_15)
; CHECK: ffffffffffffffff 0
  %ui64_16 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x0000000000000000, i64 u0xffffffffffffffff)
  call void @print_i64({i64, i1} %ui64_16)
; CHECK: ffffffffffffffff 0
  %si64_16 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x0000000000000000, i64 u0xffffffffffffffff)
  call void @print_i64({i64, i1} %si64_16)
; CHECK: 0000000000000000 0
  %ui64_17 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x0000000000000000, i64 u0x0000000000000000)
  call void @print_i64({i64, i1} %ui64_17)
; CHECK: 0000000000000000 0
  %si64_17 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x0000000000000000, i64 u0x0000000000000000)
  call void @print_i64({i64, i1} %si64_17)
; CHECK: 0000000000000001 0
  %ui64_18 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x0000000000000000, i64 u0x0000000000000001)
  call void @print_i64({i64, i1} %ui64_18)
; CHECK: 0000000000000001 0
  %si64_18 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x0000000000000000, i64 u0x0000000000000001)
  call void @print_i64({i64, i1} %si64_18)
; CHECK: 0000000000000002 0
  %ui64_19 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x0000000000000000, i64 u0x0000000000000002)
  call void @print_i64({i64, i1} %ui64_19)
; CHECK: 0000000000000002 0
  %si64_19 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x0000000000000000, i64 u0x0000000000000002)
  call void @print_i64({i64, i1} %si64_19)
; CHECK: 8000000000000000 0
  %ui64_20 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x0000000000000000, i64 u0x8000000000000000)
  call void @print_i64({i64, i1} %ui64_20)
; CHECK: 8000000000000000 0
  %si64_20 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x0000000000000000, i64 u0x8000000000000000)
  call void @print_i64({i64, i1} %si64_20)
; CHECK: 7fffffffffffffff 0
  %ui64_21 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x0000000000000000, i64 u0x7fffffffffffffff)
  call void @print_i64({i64, i1} %ui64_21)
; CHECK: 7fffffffffffffff 0
  %si64_21 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x0000000000000000, i64 u0x7fffffffffffffff)
  call void @print_i64({i64, i1} %si64_21)
; CHECK: ffffffffffffffff 0
  %ui64_22 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x0000000000000001, i64 u0xfffffffffffffffe)
  call void @print_i64({i64, i1} %ui64_22)
; CHECK: ffffffffffffffff 0
  %si64_22 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x0000000000000001, i64 u0xfffffffffffffffe)
  call void @print_i64({i64, i1} %si64_22)
; CHECK: 0000000000000000 1
  %ui64_23 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x0000000000000001, i64 u0xffffffffffffffff)
  call void @print_i64({i64, i1} %ui64_23)
; CHECK: 0000000000000000 0
  %si64_23 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x0000000000000001, i64 u0xffffffffffffffff)
  call void @print_i64({i64, i1} %si64_23)
; CHECK: 0000000000000001 0
  %ui64_24 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x0000000000000001, i64 u0x0000000000000000)
  call void @print_i64({i64, i1} %ui64_24)
; CHECK: 0000000000000001 0
  %si64_24 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x0000000000000001, i64 u0x0000000000000000)
  call void @print_i64({i64, i1} %si64_24)
; CHECK: 0000000000000002 0
  %ui64_25 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x0000000000000001, i64 u0x0000000000000001)
  call void @print_i64({i64, i1} %ui64_25)
; CHECK: 0000000000000002 0
  %si64_25 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x0000000000000001, i64 u0x0000000000000001)
  call void @print_i64({i64, i1} %si64_25)
; CHECK: 0000000000000003 0
  %ui64_26 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x0000000000000001, i64 u0x0000000000000002)
  call void @print_i64({i64, i1} %ui64_26)
; CHECK: 0000000000000003 0
  %si64_26 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x0000000000000001, i64 u0x0000000000000002)
  call void @print_i64({i64, i1} %si64_26)
; CHECK: 8000000000000001 0
  %ui64_27 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x0000000000000001, i64 u0x8000000000000000)
  call void @print_i64({i64, i1} %ui64_27)
; CHECK: 8000000000000001 0
  %si64_27 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x0000000000000001, i64 u0x8000000000000000)
  call void @print_i64({i64, i1} %si64_27)
; CHECK: 8000000000000000 0
  %ui64_28 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x0000000000000001, i64 u0x7fffffffffffffff)
  call void @print_i64({i64, i1} %ui64_28)
; CHECK: 8000000000000000 1
  %si64_28 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x0000000000000001, i64 u0x7fffffffffffffff)
  call void @print_i64({i64, i1} %si64_28)
; CHECK: 0000000000000000 1
  %ui64_29 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x0000000000000002, i64 u0xfffffffffffffffe)
  call void @print_i64({i64, i1} %ui64_29)
; CHECK: 0000000000000000 0
  %si64_29 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x0000000000000002, i64 u0xfffffffffffffffe)
  call void @print_i64({i64, i1} %si64_29)
; CHECK: 0000000000000001 1
  %ui64_30 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x0000000000000002, i64 u0xffffffffffffffff)
  call void @print_i64({i64, i1} %ui64_30)
; CHECK: 0000000000000001 0
  %si64_30 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x0000000000000002, i64 u0xffffffffffffffff)
  call void @print_i64({i64, i1} %si64_30)
; CHECK: 0000000000000002 0
  %ui64_31 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x0000000000000002, i64 u0x0000000000000000)
  call void @print_i64({i64, i1} %ui64_31)
; CHECK: 0000000000000002 0
  %si64_31 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x0000000000000002, i64 u0x0000000000000000)
  call void @print_i64({i64, i1} %si64_31)
; CHECK: 0000000000000003 0
  %ui64_32 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x0000000000000002, i64 u0x0000000000000001)
  call void @print_i64({i64, i1} %ui64_32)
; CHECK: 0000000000000003 0
  %si64_32 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x0000000000000002, i64 u0x0000000000000001)
  call void @print_i64({i64, i1} %si64_32)
; CHECK: 0000000000000004 0
  %ui64_33 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x0000000000000002, i64 u0x0000000000000002)
  call void @print_i64({i64, i1} %ui64_33)
; CHECK: 0000000000000004 0
  %si64_33 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x0000000000000002, i64 u0x0000000000000002)
  call void @print_i64({i64, i1} %si64_33)
; CHECK: 8000000000000002 0
  %ui64_34 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x0000000000000002, i64 u0x8000000000000000)
  call void @print_i64({i64, i1} %ui64_34)
; CHECK: 8000000000000002 0
  %si64_34 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x0000000000000002, i64 u0x8000000000000000)
  call void @print_i64({i64, i1} %si64_34)
; CHECK: 8000000000000001 0
  %ui64_35 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x0000000000000002, i64 u0x7fffffffffffffff)
  call void @print_i64({i64, i1} %ui64_35)
; CHECK: 8000000000000001 1
  %si64_35 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x0000000000000002, i64 u0x7fffffffffffffff)
  call void @print_i64({i64, i1} %si64_35)
; CHECK: 7ffffffffffffffe 1
  %ui64_36 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x8000000000000000, i64 u0xfffffffffffffffe)
  call void @print_i64({i64, i1} %ui64_36)
; CHECK: 7ffffffffffffffe 1
  %si64_36 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x8000000000000000, i64 u0xfffffffffffffffe)
  call void @print_i64({i64, i1} %si64_36)
; CHECK: 7fffffffffffffff 1
  %ui64_37 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x8000000000000000, i64 u0xffffffffffffffff)
  call void @print_i64({i64, i1} %ui64_37)
; CHECK: 7fffffffffffffff 1
  %si64_37 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x8000000000000000, i64 u0xffffffffffffffff)
  call void @print_i64({i64, i1} %si64_37)
; CHECK: 8000000000000000 0
  %ui64_38 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x8000000000000000, i64 u0x0000000000000000)
  call void @print_i64({i64, i1} %ui64_38)
; CHECK: 8000000000000000 0
  %si64_38 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x8000000000000000, i64 u0x0000000000000000)
  call void @print_i64({i64, i1} %si64_38)
; CHECK: 8000000000000001 0
  %ui64_39 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x8000000000000000, i64 u0x0000000000000001)
  call void @print_i64({i64, i1} %ui64_39)
; CHECK: 8000000000000001 0
  %si64_39 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x8000000000000000, i64 u0x0000000000000001)
  call void @print_i64({i64, i1} %si64_39)
; CHECK: 8000000000000002 0
  %ui64_40 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x8000000000000000, i64 u0x0000000000000002)
  call void @print_i64({i64, i1} %ui64_40)
; CHECK: 8000000000000002 0
  %si64_40 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x8000000000000000, i64 u0x0000000000000002)
  call void @print_i64({i64, i1} %si64_40)
; CHECK: 0000000000000000 1
  %ui64_41 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x8000000000000000, i64 u0x8000000000000000)
  call void @print_i64({i64, i1} %ui64_41)
; CHECK: 0000000000000000 1
  %si64_41 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x8000000000000000, i64 u0x8000000000000000)
  call void @print_i64({i64, i1} %si64_41)
; CHECK: ffffffffffffffff 0
  %ui64_42 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x8000000000000000, i64 u0x7fffffffffffffff)
  call void @print_i64({i64, i1} %ui64_42)
; CHECK: ffffffffffffffff 0
  %si64_42 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x8000000000000000, i64 u0x7fffffffffffffff)
  call void @print_i64({i64, i1} %si64_42)
; CHECK: 7ffffffffffffffd 1
  %ui64_43 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x7fffffffffffffff, i64 u0xfffffffffffffffe)
  call void @print_i64({i64, i1} %ui64_43)
; CHECK: 7ffffffffffffffd 0
  %si64_43 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x7fffffffffffffff, i64 u0xfffffffffffffffe)
  call void @print_i64({i64, i1} %si64_43)
; CHECK: 7ffffffffffffffe 1
  %ui64_44 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x7fffffffffffffff, i64 u0xffffffffffffffff)
  call void @print_i64({i64, i1} %ui64_44)
; CHECK: 7ffffffffffffffe 0
  %si64_44 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x7fffffffffffffff, i64 u0xffffffffffffffff)
  call void @print_i64({i64, i1} %si64_44)
; CHECK: 7fffffffffffffff 0
  %ui64_45 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x7fffffffffffffff, i64 u0x0000000000000000)
  call void @print_i64({i64, i1} %ui64_45)
; CHECK: 7fffffffffffffff 0
  %si64_45 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x7fffffffffffffff, i64 u0x0000000000000000)
  call void @print_i64({i64, i1} %si64_45)
; CHECK: 8000000000000000 0
  %ui64_46 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x7fffffffffffffff, i64 u0x0000000000000001)
  call void @print_i64({i64, i1} %ui64_46)
; CHECK: 8000000000000000 1
  %si64_46 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x7fffffffffffffff, i64 u0x0000000000000001)
  call void @print_i64({i64, i1} %si64_46)
; CHECK: 8000000000000001 0
  %ui64_47 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x7fffffffffffffff, i64 u0x0000000000000002)
  call void @print_i64({i64, i1} %ui64_47)
; CHECK: 8000000000000001 1
  %si64_47 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x7fffffffffffffff, i64 u0x0000000000000002)
  call void @print_i64({i64, i1} %si64_47)
; CHECK: ffffffffffffffff 0
  %ui64_48 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x7fffffffffffffff, i64 u0x8000000000000000)
  call void @print_i64({i64, i1} %ui64_48)
; CHECK: ffffffffffffffff 0
  %si64_48 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x7fffffffffffffff, i64 u0x8000000000000000)
  call void @print_i64({i64, i1} %si64_48)
; CHECK: fffffffffffffffe 0
  %ui64_49 = call {i64, i1} @llvm.uadd.with.overflow(i64 u0x7fffffffffffffff, i64 u0x7fffffffffffffff)
  call void @print_i64({i64, i1} %ui64_49)
; CHECK: fffffffffffffffe 1
  %si64_49 = call {i64, i1} @llvm.sadd.with.overflow(i64 u0x7fffffffffffffff, i64 u0x7fffffffffffffff)
  call void @print_i64({i64, i1} %si64_49)

; CHECK: 00000000000000000000000000000000 0
  %ui128_1 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_1)
; CHECK: 00000000000000000000000000000000 0
  %si128_1 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_1)
; CHECK: 00000000000000000000000000000001 0
  %ui128_2 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %ui128_2)
; CHECK: 00000000000000000000000000000001 0
  %si128_2 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %si128_2)
; CHECK: 00000000000000000000000000000002 0
  %ui128_3 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %ui128_3)
; CHECK: 00000000000000000000000000000002 0
  %si128_3 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %si128_3)
; CHECK: 00000000000000007fffffffffffffff 0
  %ui128_4 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_4)
; CHECK: 00000000000000007fffffffffffffff 0
  %si128_4 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %si128_4)
; CHECK: 00000000000000008000000000000000 0
  %ui128_5 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %ui128_5)
; CHECK: 00000000000000008000000000000000 0
  %si128_5 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %si128_5)
; CHECK: 0000000000000000fffffffffffffffe 0
  %ui128_6 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_6)
; CHECK: 0000000000000000fffffffffffffffe 0
  %si128_6 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_6)
; CHECK: 0000000000000000ffffffffffffffff 0
  %ui128_7 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_7)
; CHECK: 0000000000000000ffffffffffffffff 0
  %si128_7 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_7)
; CHECK: 00000000000000010000000000000000 0
  %ui128_8 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %ui128_8)
; CHECK: 00000000000000010000000000000000 0
  %si128_8 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %si128_8)
; CHECK: 00000000000000010000000000000001 0
  %ui128_9 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %ui128_9)
; CHECK: 00000000000000010000000000000001 0
  %si128_9 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %si128_9)
; CHECK: 00000000000000010000000000000002 0
  %ui128_10 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %ui128_10)
; CHECK: 00000000000000010000000000000002 0
  %si128_10 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %si128_10)
; CHECK: 00000000000000017fffffffffffffff 0
  %ui128_11 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_11)
; CHECK: 00000000000000017fffffffffffffff 0
  %si128_11 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %si128_11)
; CHECK: 00000000000000018000000000000000 0
  %ui128_12 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %ui128_12)
; CHECK: 00000000000000018000000000000000 0
  %si128_12 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %si128_12)
; CHECK: 0000000000000001fffffffffffffffe 0
  %ui128_13 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_13)
; CHECK: 0000000000000001fffffffffffffffe 0
  %si128_13 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_13)
; CHECK: 0000000000000001ffffffffffffffff 0
  %ui128_14 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_14)
; CHECK: 0000000000000001ffffffffffffffff 0
  %si128_14 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_14)
; CHECK: ffffffffffffffff0000000000000000 0
  %ui128_15 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %ui128_15)
; CHECK: ffffffffffffffff0000000000000000 0
  %si128_15 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %si128_15)
; CHECK: ffffffffffffffff0000000000000001 0
  %ui128_16 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %ui128_16)
; CHECK: ffffffffffffffff0000000000000001 0
  %si128_16 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %si128_16)
; CHECK: ffffffffffffffff0000000000000002 0
  %ui128_17 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %ui128_17)
; CHECK: ffffffffffffffff0000000000000002 0
  %si128_17 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %si128_17)
; CHECK: ffffffffffffffffffffffffffffffff 0
  %ui128_18 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_18)
; CHECK: ffffffffffffffffffffffffffffffff 0
  %si128_18 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_18)
; CHECK: fffffffffffffffffffffffffffffffe 0
  %ui128_19 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_19)
; CHECK: fffffffffffffffffffffffffffffffe 0
  %si128_19 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %si128_19)
; CHECK: 80000000000000000000000000000000 0
  %ui128_20 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_20)
; CHECK: 80000000000000000000000000000000 0
  %si128_20 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_20)
; CHECK: 40000000000000000000000000000000 0
  %ui128_21 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_21)
; CHECK: 40000000000000000000000000000000 0
  %si128_21 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_21)
; CHECK: 7fffffffffffffffffffffffffffffff 0
  %ui128_22 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_22)
; CHECK: 7fffffffffffffffffffffffffffffff 0
  %si128_22 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_22)
; CHECK: 7ffffffffffffff00000000000000000 0
  %ui128_23 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %ui128_23)
; CHECK: 7ffffffffffffff00000000000000000 0
  %si128_23 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %si128_23)
; CHECK: 7ffffffffffffff00000000000000001 0
  %ui128_24 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %ui128_24)
; CHECK: 7ffffffffffffff00000000000000001 0
  %si128_24 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %si128_24)
; CHECK: 3fffffffffffffffffffffffffffffff 0
  %ui128_25 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_25)
; CHECK: 3fffffffffffffffffffffffffffffff 0
  %si128_25 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000000, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_25)
; CHECK: 00000000000000000000000000000001 0
  %ui128_26 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_26)
; CHECK: 00000000000000000000000000000001 0
  %si128_26 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_26)
; CHECK: 00000000000000000000000000000002 0
  %ui128_27 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %ui128_27)
; CHECK: 00000000000000000000000000000002 0
  %si128_27 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %si128_27)
; CHECK: 00000000000000000000000000000003 0
  %ui128_28 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %ui128_28)
; CHECK: 00000000000000000000000000000003 0
  %si128_28 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %si128_28)
; CHECK: 00000000000000008000000000000000 0
  %ui128_29 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_29)
; CHECK: 00000000000000008000000000000000 0
  %si128_29 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %si128_29)
; CHECK: 00000000000000008000000000000001 0
  %ui128_30 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %ui128_30)
; CHECK: 00000000000000008000000000000001 0
  %si128_30 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %si128_30)
; CHECK: 0000000000000000ffffffffffffffff 0
  %ui128_31 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_31)
; CHECK: 0000000000000000ffffffffffffffff 0
  %si128_31 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_31)
; CHECK: 00000000000000010000000000000000 0
  %ui128_32 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_32)
; CHECK: 00000000000000010000000000000000 0
  %si128_32 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_32)
; CHECK: 00000000000000010000000000000001 0
  %ui128_33 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %ui128_33)
; CHECK: 00000000000000010000000000000001 0
  %si128_33 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %si128_33)
; CHECK: 00000000000000010000000000000002 0
  %ui128_34 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %ui128_34)
; CHECK: 00000000000000010000000000000002 0
  %si128_34 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %si128_34)
; CHECK: 00000000000000010000000000000003 0
  %ui128_35 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %ui128_35)
; CHECK: 00000000000000010000000000000003 0
  %si128_35 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %si128_35)
; CHECK: 00000000000000018000000000000000 0
  %ui128_36 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_36)
; CHECK: 00000000000000018000000000000000 0
  %si128_36 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %si128_36)
; CHECK: 00000000000000018000000000000001 0
  %ui128_37 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %ui128_37)
; CHECK: 00000000000000018000000000000001 0
  %si128_37 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %si128_37)
; CHECK: 0000000000000001ffffffffffffffff 0
  %ui128_38 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_38)
; CHECK: 0000000000000001ffffffffffffffff 0
  %si128_38 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_38)
; CHECK: 00000000000000020000000000000000 0
  %ui128_39 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_39)
; CHECK: 00000000000000020000000000000000 0
  %si128_39 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_39)
; CHECK: ffffffffffffffff0000000000000001 0
  %ui128_40 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %ui128_40)
; CHECK: ffffffffffffffff0000000000000001 0
  %si128_40 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %si128_40)
; CHECK: ffffffffffffffff0000000000000002 0
  %ui128_41 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %ui128_41)
; CHECK: ffffffffffffffff0000000000000002 0
  %si128_41 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %si128_41)
; CHECK: ffffffffffffffff0000000000000003 0
  %ui128_42 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %ui128_42)
; CHECK: ffffffffffffffff0000000000000003 0
  %si128_42 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %si128_42)
; CHECK: 00000000000000000000000000000000 1
  %ui128_43 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_43)
; CHECK: 00000000000000000000000000000000 0
  %si128_43 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_43)
; CHECK: ffffffffffffffffffffffffffffffff 0
  %ui128_44 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_44)
; CHECK: ffffffffffffffffffffffffffffffff 0
  %si128_44 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %si128_44)
; CHECK: 80000000000000000000000000000001 0
  %ui128_45 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_45)
; CHECK: 80000000000000000000000000000001 0
  %si128_45 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_45)
; CHECK: 40000000000000000000000000000001 0
  %ui128_46 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_46)
; CHECK: 40000000000000000000000000000001 0
  %si128_46 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_46)
; CHECK: 80000000000000000000000000000000 0
  %ui128_47 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_47)
; CHECK: 80000000000000000000000000000000 1
  %si128_47 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_47)
; CHECK: 7ffffffffffffff00000000000000001 0
  %ui128_48 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %ui128_48)
; CHECK: 7ffffffffffffff00000000000000001 0
  %si128_48 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %si128_48)
; CHECK: 7ffffffffffffff00000000000000002 0
  %ui128_49 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %ui128_49)
; CHECK: 7ffffffffffffff00000000000000002 0
  %si128_49 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %si128_49)
; CHECK: 40000000000000000000000000000000 0
  %ui128_50 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_50)
; CHECK: 40000000000000000000000000000000 0
  %si128_50 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000001, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_50)
; CHECK: 00000000000000000000000000000002 0
  %ui128_51 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_51)
; CHECK: 00000000000000000000000000000002 0
  %si128_51 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_51)
; CHECK: 00000000000000000000000000000003 0
  %ui128_52 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %ui128_52)
; CHECK: 00000000000000000000000000000003 0
  %si128_52 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %si128_52)
; CHECK: 00000000000000000000000000000004 0
  %ui128_53 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %ui128_53)
; CHECK: 00000000000000000000000000000004 0
  %si128_53 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %si128_53)
; CHECK: 00000000000000008000000000000001 0
  %ui128_54 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_54)
; CHECK: 00000000000000008000000000000001 0
  %si128_54 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %si128_54)
; CHECK: 00000000000000008000000000000002 0
  %ui128_55 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %ui128_55)
; CHECK: 00000000000000008000000000000002 0
  %si128_55 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %si128_55)
; CHECK: 00000000000000010000000000000000 0
  %ui128_56 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_56)
; CHECK: 00000000000000010000000000000000 0
  %si128_56 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_56)
; CHECK: 00000000000000010000000000000001 0
  %ui128_57 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_57)
; CHECK: 00000000000000010000000000000001 0
  %si128_57 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_57)
; CHECK: 00000000000000010000000000000002 0
  %ui128_58 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %ui128_58)
; CHECK: 00000000000000010000000000000002 0
  %si128_58 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %si128_58)
; CHECK: 00000000000000010000000000000003 0
  %ui128_59 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %ui128_59)
; CHECK: 00000000000000010000000000000003 0
  %si128_59 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %si128_59)
; CHECK: 00000000000000010000000000000004 0
  %ui128_60 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %ui128_60)
; CHECK: 00000000000000010000000000000004 0
  %si128_60 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %si128_60)
; CHECK: 00000000000000018000000000000001 0
  %ui128_61 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_61)
; CHECK: 00000000000000018000000000000001 0
  %si128_61 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %si128_61)
; CHECK: 00000000000000018000000000000002 0
  %ui128_62 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %ui128_62)
; CHECK: 00000000000000018000000000000002 0
  %si128_62 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %si128_62)
; CHECK: 00000000000000020000000000000000 0
  %ui128_63 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_63)
; CHECK: 00000000000000020000000000000000 0
  %si128_63 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_63)
; CHECK: 00000000000000020000000000000001 0
  %ui128_64 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_64)
; CHECK: 00000000000000020000000000000001 0
  %si128_64 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_64)
; CHECK: ffffffffffffffff0000000000000002 0
  %ui128_65 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %ui128_65)
; CHECK: ffffffffffffffff0000000000000002 0
  %si128_65 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %si128_65)
; CHECK: ffffffffffffffff0000000000000003 0
  %ui128_66 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %ui128_66)
; CHECK: ffffffffffffffff0000000000000003 0
  %si128_66 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %si128_66)
; CHECK: ffffffffffffffff0000000000000004 0
  %ui128_67 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %ui128_67)
; CHECK: ffffffffffffffff0000000000000004 0
  %si128_67 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %si128_67)
; CHECK: 00000000000000000000000000000001 1
  %ui128_68 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_68)
; CHECK: 00000000000000000000000000000001 0
  %si128_68 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_68)
; CHECK: 00000000000000000000000000000000 1
  %ui128_69 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_69)
; CHECK: 00000000000000000000000000000000 0
  %si128_69 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %si128_69)
; CHECK: 80000000000000000000000000000002 0
  %ui128_70 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_70)
; CHECK: 80000000000000000000000000000002 0
  %si128_70 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_70)
; CHECK: 40000000000000000000000000000002 0
  %ui128_71 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_71)
; CHECK: 40000000000000000000000000000002 0
  %si128_71 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_71)
; CHECK: 80000000000000000000000000000001 0
  %ui128_72 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_72)
; CHECK: 80000000000000000000000000000001 1
  %si128_72 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_72)
; CHECK: 7ffffffffffffff00000000000000002 0
  %ui128_73 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %ui128_73)
; CHECK: 7ffffffffffffff00000000000000002 0
  %si128_73 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %si128_73)
; CHECK: 7ffffffffffffff00000000000000003 0
  %ui128_74 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %ui128_74)
; CHECK: 7ffffffffffffff00000000000000003 0
  %si128_74 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %si128_74)
; CHECK: 40000000000000000000000000000001 0
  %ui128_75 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_75)
; CHECK: 40000000000000000000000000000001 0
  %si128_75 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000000000000000000002, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_75)
; CHECK: 00000000000000007fffffffffffffff 0
  %ui128_76 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_76)
; CHECK: 00000000000000007fffffffffffffff 0
  %si128_76 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_76)
; CHECK: 00000000000000008000000000000000 0
  %ui128_77 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %ui128_77)
; CHECK: 00000000000000008000000000000000 0
  %si128_77 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %si128_77)
; CHECK: 00000000000000008000000000000001 0
  %ui128_78 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %ui128_78)
; CHECK: 00000000000000008000000000000001 0
  %si128_78 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %si128_78)
; CHECK: 0000000000000000fffffffffffffffe 0
  %ui128_79 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_79)
; CHECK: 0000000000000000fffffffffffffffe 0
  %si128_79 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %si128_79)
; CHECK: 0000000000000000ffffffffffffffff 0
  %ui128_80 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %ui128_80)
; CHECK: 0000000000000000ffffffffffffffff 0
  %si128_80 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %si128_80)
; CHECK: 00000000000000017ffffffffffffffd 0
  %ui128_81 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_81)
; CHECK: 00000000000000017ffffffffffffffd 0
  %si128_81 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_81)
; CHECK: 00000000000000017ffffffffffffffe 0
  %ui128_82 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_82)
; CHECK: 00000000000000017ffffffffffffffe 0
  %si128_82 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_82)
; CHECK: 00000000000000017fffffffffffffff 0
  %ui128_83 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %ui128_83)
; CHECK: 00000000000000017fffffffffffffff 0
  %si128_83 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %si128_83)
; CHECK: 00000000000000018000000000000000 0
  %ui128_84 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %ui128_84)
; CHECK: 00000000000000018000000000000000 0
  %si128_84 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %si128_84)
; CHECK: 00000000000000018000000000000001 0
  %ui128_85 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %ui128_85)
; CHECK: 00000000000000018000000000000001 0
  %si128_85 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %si128_85)
; CHECK: 0000000000000001fffffffffffffffe 0
  %ui128_86 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_86)
; CHECK: 0000000000000001fffffffffffffffe 0
  %si128_86 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %si128_86)
; CHECK: 0000000000000001ffffffffffffffff 0
  %ui128_87 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %ui128_87)
; CHECK: 0000000000000001ffffffffffffffff 0
  %si128_87 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %si128_87)
; CHECK: 00000000000000027ffffffffffffffd 0
  %ui128_88 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_88)
; CHECK: 00000000000000027ffffffffffffffd 0
  %si128_88 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_88)
; CHECK: 00000000000000027ffffffffffffffe 0
  %ui128_89 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_89)
; CHECK: 00000000000000027ffffffffffffffe 0
  %si128_89 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_89)
; CHECK: ffffffffffffffff7fffffffffffffff 0
  %ui128_90 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %ui128_90)
; CHECK: ffffffffffffffff7fffffffffffffff 0
  %si128_90 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %si128_90)
; CHECK: ffffffffffffffff8000000000000000 0
  %ui128_91 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %ui128_91)
; CHECK: ffffffffffffffff8000000000000000 0
  %si128_91 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %si128_91)
; CHECK: ffffffffffffffff8000000000000001 0
  %ui128_92 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %ui128_92)
; CHECK: ffffffffffffffff8000000000000001 0
  %si128_92 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %si128_92)
; CHECK: 00000000000000007ffffffffffffffe 1
  %ui128_93 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_93)
; CHECK: 00000000000000007ffffffffffffffe 0
  %si128_93 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_93)
; CHECK: 00000000000000007ffffffffffffffd 1
  %ui128_94 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_94)
; CHECK: 00000000000000007ffffffffffffffd 0
  %si128_94 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %si128_94)
; CHECK: 80000000000000007fffffffffffffff 0
  %ui128_95 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_95)
; CHECK: 80000000000000007fffffffffffffff 0
  %si128_95 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_95)
; CHECK: 40000000000000007fffffffffffffff 0
  %ui128_96 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_96)
; CHECK: 40000000000000007fffffffffffffff 0
  %si128_96 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_96)
; CHECK: 80000000000000007ffffffffffffffe 0
  %ui128_97 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_97)
; CHECK: 80000000000000007ffffffffffffffe 1
  %si128_97 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_97)
; CHECK: 7ffffffffffffff07fffffffffffffff 0
  %ui128_98 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %ui128_98)
; CHECK: 7ffffffffffffff07fffffffffffffff 0
  %si128_98 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %si128_98)
; CHECK: 7ffffffffffffff08000000000000000 0
  %ui128_99 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %ui128_99)
; CHECK: 7ffffffffffffff08000000000000000 0
  %si128_99 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %si128_99)
; CHECK: 40000000000000007ffffffffffffffe 0
  %ui128_100 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_100)
; CHECK: 40000000000000007ffffffffffffffe 0
  %si128_100 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000007fffffffffffffff, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_100)
; CHECK: 00000000000000008000000000000000 0
  %ui128_101 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_101)
; CHECK: 00000000000000008000000000000000 0
  %si128_101 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_101)
; CHECK: 00000000000000008000000000000001 0
  %ui128_102 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %ui128_102)
; CHECK: 00000000000000008000000000000001 0
  %si128_102 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %si128_102)
; CHECK: 00000000000000008000000000000002 0
  %ui128_103 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %ui128_103)
; CHECK: 00000000000000008000000000000002 0
  %si128_103 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %si128_103)
; CHECK: 0000000000000000ffffffffffffffff 0
  %ui128_104 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_104)
; CHECK: 0000000000000000ffffffffffffffff 0
  %si128_104 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %si128_104)
; CHECK: 00000000000000010000000000000000 0
  %ui128_105 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %ui128_105)
; CHECK: 00000000000000010000000000000000 0
  %si128_105 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %si128_105)
; CHECK: 00000000000000017ffffffffffffffe 0
  %ui128_106 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_106)
; CHECK: 00000000000000017ffffffffffffffe 0
  %si128_106 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_106)
; CHECK: 00000000000000017fffffffffffffff 0
  %ui128_107 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_107)
; CHECK: 00000000000000017fffffffffffffff 0
  %si128_107 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_107)
; CHECK: 00000000000000018000000000000000 0
  %ui128_108 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %ui128_108)
; CHECK: 00000000000000018000000000000000 0
  %si128_108 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %si128_108)
; CHECK: 00000000000000018000000000000001 0
  %ui128_109 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %ui128_109)
; CHECK: 00000000000000018000000000000001 0
  %si128_109 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %si128_109)
; CHECK: 00000000000000018000000000000002 0
  %ui128_110 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %ui128_110)
; CHECK: 00000000000000018000000000000002 0
  %si128_110 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %si128_110)
; CHECK: 0000000000000001ffffffffffffffff 0
  %ui128_111 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_111)
; CHECK: 0000000000000001ffffffffffffffff 0
  %si128_111 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %si128_111)
; CHECK: 00000000000000020000000000000000 0
  %ui128_112 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %ui128_112)
; CHECK: 00000000000000020000000000000000 0
  %si128_112 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %si128_112)
; CHECK: 00000000000000027ffffffffffffffe 0
  %ui128_113 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_113)
; CHECK: 00000000000000027ffffffffffffffe 0
  %si128_113 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_113)
; CHECK: 00000000000000027fffffffffffffff 0
  %ui128_114 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_114)
; CHECK: 00000000000000027fffffffffffffff 0
  %si128_114 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_114)
; CHECK: ffffffffffffffff8000000000000000 0
  %ui128_115 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %ui128_115)
; CHECK: ffffffffffffffff8000000000000000 0
  %si128_115 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %si128_115)
; CHECK: ffffffffffffffff8000000000000001 0
  %ui128_116 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %ui128_116)
; CHECK: ffffffffffffffff8000000000000001 0
  %si128_116 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %si128_116)
; CHECK: ffffffffffffffff8000000000000002 0
  %ui128_117 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %ui128_117)
; CHECK: ffffffffffffffff8000000000000002 0
  %si128_117 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %si128_117)
; CHECK: 00000000000000007fffffffffffffff 1
  %ui128_118 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_118)
; CHECK: 00000000000000007fffffffffffffff 0
  %si128_118 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_118)
; CHECK: 00000000000000007ffffffffffffffe 1
  %ui128_119 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_119)
; CHECK: 00000000000000007ffffffffffffffe 0
  %si128_119 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %si128_119)
; CHECK: 80000000000000008000000000000000 0
  %ui128_120 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_120)
; CHECK: 80000000000000008000000000000000 0
  %si128_120 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_120)
; CHECK: 40000000000000008000000000000000 0
  %ui128_121 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_121)
; CHECK: 40000000000000008000000000000000 0
  %si128_121 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_121)
; CHECK: 80000000000000007fffffffffffffff 0
  %ui128_122 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_122)
; CHECK: 80000000000000007fffffffffffffff 1
  %si128_122 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_122)
; CHECK: 7ffffffffffffff08000000000000000 0
  %ui128_123 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %ui128_123)
; CHECK: 7ffffffffffffff08000000000000000 0
  %si128_123 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %si128_123)
; CHECK: 7ffffffffffffff08000000000000001 0
  %ui128_124 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %ui128_124)
; CHECK: 7ffffffffffffff08000000000000001 0
  %si128_124 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %si128_124)
; CHECK: 40000000000000007fffffffffffffff 0
  %ui128_125 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_125)
; CHECK: 40000000000000007fffffffffffffff 0
  %si128_125 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000008000000000000000, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_125)
; CHECK: 0000000000000000fffffffffffffffe 0
  %ui128_126 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_126)
; CHECK: 0000000000000000fffffffffffffffe 0
  %si128_126 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_126)
; CHECK: 0000000000000000ffffffffffffffff 0
  %ui128_127 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %ui128_127)
; CHECK: 0000000000000000ffffffffffffffff 0
  %si128_127 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %si128_127)
; CHECK: 00000000000000010000000000000000 0
  %ui128_128 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %ui128_128)
; CHECK: 00000000000000010000000000000000 0
  %si128_128 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %si128_128)
; CHECK: 00000000000000017ffffffffffffffd 0
  %ui128_129 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_129)
; CHECK: 00000000000000017ffffffffffffffd 0
  %si128_129 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %si128_129)
; CHECK: 00000000000000017ffffffffffffffe 0
  %ui128_130 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %ui128_130)
; CHECK: 00000000000000017ffffffffffffffe 0
  %si128_130 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %si128_130)
; CHECK: 0000000000000001fffffffffffffffc 0
  %ui128_131 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_131)
; CHECK: 0000000000000001fffffffffffffffc 0
  %si128_131 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_131)
; CHECK: 0000000000000001fffffffffffffffd 0
  %ui128_132 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_132)
; CHECK: 0000000000000001fffffffffffffffd 0
  %si128_132 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_132)
; CHECK: 0000000000000001fffffffffffffffe 0
  %ui128_133 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %ui128_133)
; CHECK: 0000000000000001fffffffffffffffe 0
  %si128_133 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %si128_133)
; CHECK: 0000000000000001ffffffffffffffff 0
  %ui128_134 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %ui128_134)
; CHECK: 0000000000000001ffffffffffffffff 0
  %si128_134 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %si128_134)
; CHECK: 00000000000000020000000000000000 0
  %ui128_135 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %ui128_135)
; CHECK: 00000000000000020000000000000000 0
  %si128_135 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %si128_135)
; CHECK: 00000000000000027ffffffffffffffd 0
  %ui128_136 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_136)
; CHECK: 00000000000000027ffffffffffffffd 0
  %si128_136 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %si128_136)
; CHECK: 00000000000000027ffffffffffffffe 0
  %ui128_137 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %ui128_137)
; CHECK: 00000000000000027ffffffffffffffe 0
  %si128_137 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %si128_137)
; CHECK: 0000000000000002fffffffffffffffc 0
  %ui128_138 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_138)
; CHECK: 0000000000000002fffffffffffffffc 0
  %si128_138 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_138)
; CHECK: 0000000000000002fffffffffffffffd 0
  %ui128_139 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_139)
; CHECK: 0000000000000002fffffffffffffffd 0
  %si128_139 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_139)
; CHECK: fffffffffffffffffffffffffffffffe 0
  %ui128_140 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %ui128_140)
; CHECK: fffffffffffffffffffffffffffffffe 0
  %si128_140 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %si128_140)
; CHECK: ffffffffffffffffffffffffffffffff 0
  %ui128_141 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %ui128_141)
; CHECK: ffffffffffffffffffffffffffffffff 0
  %si128_141 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %si128_141)
; CHECK: 00000000000000000000000000000000 1
  %ui128_142 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %ui128_142)
; CHECK: 00000000000000000000000000000000 0
  %si128_142 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %si128_142)
; CHECK: 0000000000000000fffffffffffffffd 1
  %ui128_143 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_143)
; CHECK: 0000000000000000fffffffffffffffd 0
  %si128_143 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_143)
; CHECK: 0000000000000000fffffffffffffffc 1
  %ui128_144 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_144)
; CHECK: 0000000000000000fffffffffffffffc 0
  %si128_144 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %si128_144)
; CHECK: 8000000000000000fffffffffffffffe 0
  %ui128_145 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_145)
; CHECK: 8000000000000000fffffffffffffffe 0
  %si128_145 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_145)
; CHECK: 4000000000000000fffffffffffffffe 0
  %ui128_146 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_146)
; CHECK: 4000000000000000fffffffffffffffe 0
  %si128_146 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_146)
; CHECK: 8000000000000000fffffffffffffffd 0
  %ui128_147 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_147)
; CHECK: 8000000000000000fffffffffffffffd 1
  %si128_147 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_147)
; CHECK: 7ffffffffffffff0fffffffffffffffe 0
  %ui128_148 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %ui128_148)
; CHECK: 7ffffffffffffff0fffffffffffffffe 0
  %si128_148 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %si128_148)
; CHECK: 7ffffffffffffff0ffffffffffffffff 0
  %ui128_149 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %ui128_149)
; CHECK: 7ffffffffffffff0ffffffffffffffff 0
  %si128_149 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %si128_149)
; CHECK: 4000000000000000fffffffffffffffd 0
  %ui128_150 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_150)
; CHECK: 4000000000000000fffffffffffffffd 0
  %si128_150 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000fffffffffffffffe, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_150)
; CHECK: 0000000000000000ffffffffffffffff 0
  %ui128_151 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_151)
; CHECK: 0000000000000000ffffffffffffffff 0
  %si128_151 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_151)
; CHECK: 00000000000000010000000000000000 0
  %ui128_152 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %ui128_152)
; CHECK: 00000000000000010000000000000000 0
  %si128_152 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %si128_152)
; CHECK: 00000000000000010000000000000001 0
  %ui128_153 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %ui128_153)
; CHECK: 00000000000000010000000000000001 0
  %si128_153 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %si128_153)
; CHECK: 00000000000000017ffffffffffffffe 0
  %ui128_154 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_154)
; CHECK: 00000000000000017ffffffffffffffe 0
  %si128_154 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %si128_154)
; CHECK: 00000000000000017fffffffffffffff 0
  %ui128_155 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %ui128_155)
; CHECK: 00000000000000017fffffffffffffff 0
  %si128_155 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %si128_155)
; CHECK: 0000000000000001fffffffffffffffd 0
  %ui128_156 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_156)
; CHECK: 0000000000000001fffffffffffffffd 0
  %si128_156 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_156)
; CHECK: 0000000000000001fffffffffffffffe 0
  %ui128_157 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_157)
; CHECK: 0000000000000001fffffffffffffffe 0
  %si128_157 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_157)
; CHECK: 0000000000000001ffffffffffffffff 0
  %ui128_158 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %ui128_158)
; CHECK: 0000000000000001ffffffffffffffff 0
  %si128_158 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %si128_158)
; CHECK: 00000000000000020000000000000000 0
  %ui128_159 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %ui128_159)
; CHECK: 00000000000000020000000000000000 0
  %si128_159 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %si128_159)
; CHECK: 00000000000000020000000000000001 0
  %ui128_160 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %ui128_160)
; CHECK: 00000000000000020000000000000001 0
  %si128_160 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %si128_160)
; CHECK: 00000000000000027ffffffffffffffe 0
  %ui128_161 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_161)
; CHECK: 00000000000000027ffffffffffffffe 0
  %si128_161 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %si128_161)
; CHECK: 00000000000000027fffffffffffffff 0
  %ui128_162 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %ui128_162)
; CHECK: 00000000000000027fffffffffffffff 0
  %si128_162 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %si128_162)
; CHECK: 0000000000000002fffffffffffffffd 0
  %ui128_163 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_163)
; CHECK: 0000000000000002fffffffffffffffd 0
  %si128_163 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_163)
; CHECK: 0000000000000002fffffffffffffffe 0
  %ui128_164 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_164)
; CHECK: 0000000000000002fffffffffffffffe 0
  %si128_164 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_164)
; CHECK: ffffffffffffffffffffffffffffffff 0
  %ui128_165 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %ui128_165)
; CHECK: ffffffffffffffffffffffffffffffff 0
  %si128_165 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %si128_165)
; CHECK: 00000000000000000000000000000000 1
  %ui128_166 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %ui128_166)
; CHECK: 00000000000000000000000000000000 0
  %si128_166 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %si128_166)
; CHECK: 00000000000000000000000000000001 1
  %ui128_167 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %ui128_167)
; CHECK: 00000000000000000000000000000001 0
  %si128_167 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %si128_167)
; CHECK: 0000000000000000fffffffffffffffe 1
  %ui128_168 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_168)
; CHECK: 0000000000000000fffffffffffffffe 0
  %si128_168 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_168)
; CHECK: 0000000000000000fffffffffffffffd 1
  %ui128_169 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_169)
; CHECK: 0000000000000000fffffffffffffffd 0
  %si128_169 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %si128_169)
; CHECK: 8000000000000000ffffffffffffffff 0
  %ui128_170 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_170)
; CHECK: 8000000000000000ffffffffffffffff 0
  %si128_170 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_170)
; CHECK: 4000000000000000ffffffffffffffff 0
  %ui128_171 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_171)
; CHECK: 4000000000000000ffffffffffffffff 0
  %si128_171 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_171)
; CHECK: 8000000000000000fffffffffffffffe 0
  %ui128_172 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_172)
; CHECK: 8000000000000000fffffffffffffffe 1
  %si128_172 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_172)
; CHECK: 7ffffffffffffff0ffffffffffffffff 0
  %ui128_173 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %ui128_173)
; CHECK: 7ffffffffffffff0ffffffffffffffff 0
  %si128_173 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %si128_173)
; CHECK: 7ffffffffffffff10000000000000000 0
  %ui128_174 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %ui128_174)
; CHECK: 7ffffffffffffff10000000000000000 0
  %si128_174 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %si128_174)
; CHECK: 4000000000000000fffffffffffffffe 0
  %ui128_175 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_175)
; CHECK: 4000000000000000fffffffffffffffe 0
  %si128_175 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000000ffffffffffffffff, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_175)
; CHECK: 00000000000000010000000000000000 0
  %ui128_176 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_176)
; CHECK: 00000000000000010000000000000000 0
  %si128_176 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_176)
; CHECK: 00000000000000010000000000000001 0
  %ui128_177 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %ui128_177)
; CHECK: 00000000000000010000000000000001 0
  %si128_177 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %si128_177)
; CHECK: 00000000000000010000000000000002 0
  %ui128_178 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %ui128_178)
; CHECK: 00000000000000010000000000000002 0
  %si128_178 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %si128_178)
; CHECK: 00000000000000017fffffffffffffff 0
  %ui128_179 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_179)
; CHECK: 00000000000000017fffffffffffffff 0
  %si128_179 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %si128_179)
; CHECK: 00000000000000018000000000000000 0
  %ui128_180 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %ui128_180)
; CHECK: 00000000000000018000000000000000 0
  %si128_180 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %si128_180)
; CHECK: 0000000000000001fffffffffffffffe 0
  %ui128_181 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_181)
; CHECK: 0000000000000001fffffffffffffffe 0
  %si128_181 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_181)
; CHECK: 0000000000000001ffffffffffffffff 0
  %ui128_182 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_182)
; CHECK: 0000000000000001ffffffffffffffff 0
  %si128_182 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_182)
; CHECK: 00000000000000020000000000000000 0
  %ui128_183 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %ui128_183)
; CHECK: 00000000000000020000000000000000 0
  %si128_183 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %si128_183)
; CHECK: 00000000000000020000000000000001 0
  %ui128_184 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %ui128_184)
; CHECK: 00000000000000020000000000000001 0
  %si128_184 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %si128_184)
; CHECK: 00000000000000020000000000000002 0
  %ui128_185 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %ui128_185)
; CHECK: 00000000000000020000000000000002 0
  %si128_185 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %si128_185)
; CHECK: 00000000000000027fffffffffffffff 0
  %ui128_186 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_186)
; CHECK: 00000000000000027fffffffffffffff 0
  %si128_186 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %si128_186)
; CHECK: 00000000000000028000000000000000 0
  %ui128_187 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %ui128_187)
; CHECK: 00000000000000028000000000000000 0
  %si128_187 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %si128_187)
; CHECK: 0000000000000002fffffffffffffffe 0
  %ui128_188 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_188)
; CHECK: 0000000000000002fffffffffffffffe 0
  %si128_188 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_188)
; CHECK: 0000000000000002ffffffffffffffff 0
  %ui128_189 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_189)
; CHECK: 0000000000000002ffffffffffffffff 0
  %si128_189 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_189)
; CHECK: 00000000000000000000000000000000 1
  %ui128_190 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %ui128_190)
; CHECK: 00000000000000000000000000000000 0
  %si128_190 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %si128_190)
; CHECK: 00000000000000000000000000000001 1
  %ui128_191 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %ui128_191)
; CHECK: 00000000000000000000000000000001 0
  %si128_191 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %si128_191)
; CHECK: 00000000000000000000000000000002 1
  %ui128_192 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %ui128_192)
; CHECK: 00000000000000000000000000000002 0
  %si128_192 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %si128_192)
; CHECK: 0000000000000000ffffffffffffffff 1
  %ui128_193 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_193)
; CHECK: 0000000000000000ffffffffffffffff 0
  %si128_193 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_193)
; CHECK: 0000000000000000fffffffffffffffe 1
  %ui128_194 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_194)
; CHECK: 0000000000000000fffffffffffffffe 0
  %si128_194 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %si128_194)
; CHECK: 80000000000000010000000000000000 0
  %ui128_195 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_195)
; CHECK: 80000000000000010000000000000000 0
  %si128_195 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_195)
; CHECK: 40000000000000010000000000000000 0
  %ui128_196 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_196)
; CHECK: 40000000000000010000000000000000 0
  %si128_196 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_196)
; CHECK: 8000000000000000ffffffffffffffff 0
  %ui128_197 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_197)
; CHECK: 8000000000000000ffffffffffffffff 1
  %si128_197 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_197)
; CHECK: 7ffffffffffffff10000000000000000 0
  %ui128_198 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %ui128_198)
; CHECK: 7ffffffffffffff10000000000000000 0
  %si128_198 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %si128_198)
; CHECK: 7ffffffffffffff10000000000000001 0
  %ui128_199 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %ui128_199)
; CHECK: 7ffffffffffffff10000000000000001 0
  %si128_199 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %si128_199)
; CHECK: 4000000000000000ffffffffffffffff 0
  %ui128_200 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_200)
; CHECK: 4000000000000000ffffffffffffffff 0
  %si128_200 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000000, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_200)
; CHECK: 00000000000000010000000000000001 0
  %ui128_201 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_201)
; CHECK: 00000000000000010000000000000001 0
  %si128_201 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_201)
; CHECK: 00000000000000010000000000000002 0
  %ui128_202 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %ui128_202)
; CHECK: 00000000000000010000000000000002 0
  %si128_202 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %si128_202)
; CHECK: 00000000000000010000000000000003 0
  %ui128_203 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %ui128_203)
; CHECK: 00000000000000010000000000000003 0
  %si128_203 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %si128_203)
; CHECK: 00000000000000018000000000000000 0
  %ui128_204 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_204)
; CHECK: 00000000000000018000000000000000 0
  %si128_204 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %si128_204)
; CHECK: 00000000000000018000000000000001 0
  %ui128_205 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %ui128_205)
; CHECK: 00000000000000018000000000000001 0
  %si128_205 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %si128_205)
; CHECK: 0000000000000001ffffffffffffffff 0
  %ui128_206 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_206)
; CHECK: 0000000000000001ffffffffffffffff 0
  %si128_206 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_206)
; CHECK: 00000000000000020000000000000000 0
  %ui128_207 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_207)
; CHECK: 00000000000000020000000000000000 0
  %si128_207 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_207)
; CHECK: 00000000000000020000000000000001 0
  %ui128_208 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %ui128_208)
; CHECK: 00000000000000020000000000000001 0
  %si128_208 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %si128_208)
; CHECK: 00000000000000020000000000000002 0
  %ui128_209 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %ui128_209)
; CHECK: 00000000000000020000000000000002 0
  %si128_209 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %si128_209)
; CHECK: 00000000000000020000000000000003 0
  %ui128_210 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %ui128_210)
; CHECK: 00000000000000020000000000000003 0
  %si128_210 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %si128_210)
; CHECK: 00000000000000028000000000000000 0
  %ui128_211 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_211)
; CHECK: 00000000000000028000000000000000 0
  %si128_211 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %si128_211)
; CHECK: 00000000000000028000000000000001 0
  %ui128_212 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %ui128_212)
; CHECK: 00000000000000028000000000000001 0
  %si128_212 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %si128_212)
; CHECK: 0000000000000002ffffffffffffffff 0
  %ui128_213 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_213)
; CHECK: 0000000000000002ffffffffffffffff 0
  %si128_213 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_213)
; CHECK: 00000000000000030000000000000000 0
  %ui128_214 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_214)
; CHECK: 00000000000000030000000000000000 0
  %si128_214 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_214)
; CHECK: 00000000000000000000000000000001 1
  %ui128_215 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %ui128_215)
; CHECK: 00000000000000000000000000000001 0
  %si128_215 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %si128_215)
; CHECK: 00000000000000000000000000000002 1
  %ui128_216 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %ui128_216)
; CHECK: 00000000000000000000000000000002 0
  %si128_216 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %si128_216)
; CHECK: 00000000000000000000000000000003 1
  %ui128_217 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %ui128_217)
; CHECK: 00000000000000000000000000000003 0
  %si128_217 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %si128_217)
; CHECK: 00000000000000010000000000000000 1
  %ui128_218 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_218)
; CHECK: 00000000000000010000000000000000 0
  %si128_218 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_218)
; CHECK: 0000000000000000ffffffffffffffff 1
  %ui128_219 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_219)
; CHECK: 0000000000000000ffffffffffffffff 0
  %si128_219 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %si128_219)
; CHECK: 80000000000000010000000000000001 0
  %ui128_220 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_220)
; CHECK: 80000000000000010000000000000001 0
  %si128_220 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_220)
; CHECK: 40000000000000010000000000000001 0
  %ui128_221 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_221)
; CHECK: 40000000000000010000000000000001 0
  %si128_221 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_221)
; CHECK: 80000000000000010000000000000000 0
  %ui128_222 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_222)
; CHECK: 80000000000000010000000000000000 1
  %si128_222 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_222)
; CHECK: 7ffffffffffffff10000000000000001 0
  %ui128_223 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %ui128_223)
; CHECK: 7ffffffffffffff10000000000000001 0
  %si128_223 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %si128_223)
; CHECK: 7ffffffffffffff10000000000000002 0
  %ui128_224 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %ui128_224)
; CHECK: 7ffffffffffffff10000000000000002 0
  %si128_224 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %si128_224)
; CHECK: 40000000000000010000000000000000 0
  %ui128_225 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_225)
; CHECK: 40000000000000010000000000000000 0
  %si128_225 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000001, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_225)
; CHECK: 00000000000000010000000000000002 0
  %ui128_226 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_226)
; CHECK: 00000000000000010000000000000002 0
  %si128_226 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_226)
; CHECK: 00000000000000010000000000000003 0
  %ui128_227 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %ui128_227)
; CHECK: 00000000000000010000000000000003 0
  %si128_227 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %si128_227)
; CHECK: 00000000000000010000000000000004 0
  %ui128_228 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %ui128_228)
; CHECK: 00000000000000010000000000000004 0
  %si128_228 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %si128_228)
; CHECK: 00000000000000018000000000000001 0
  %ui128_229 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_229)
; CHECK: 00000000000000018000000000000001 0
  %si128_229 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %si128_229)
; CHECK: 00000000000000018000000000000002 0
  %ui128_230 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %ui128_230)
; CHECK: 00000000000000018000000000000002 0
  %si128_230 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %si128_230)
; CHECK: 00000000000000020000000000000000 0
  %ui128_231 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_231)
; CHECK: 00000000000000020000000000000000 0
  %si128_231 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_231)
; CHECK: 00000000000000020000000000000001 0
  %ui128_232 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_232)
; CHECK: 00000000000000020000000000000001 0
  %si128_232 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_232)
; CHECK: 00000000000000020000000000000002 0
  %ui128_233 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %ui128_233)
; CHECK: 00000000000000020000000000000002 0
  %si128_233 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %si128_233)
; CHECK: 00000000000000020000000000000003 0
  %ui128_234 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %ui128_234)
; CHECK: 00000000000000020000000000000003 0
  %si128_234 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %si128_234)
; CHECK: 00000000000000020000000000000004 0
  %ui128_235 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %ui128_235)
; CHECK: 00000000000000020000000000000004 0
  %si128_235 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %si128_235)
; CHECK: 00000000000000028000000000000001 0
  %ui128_236 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_236)
; CHECK: 00000000000000028000000000000001 0
  %si128_236 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %si128_236)
; CHECK: 00000000000000028000000000000002 0
  %ui128_237 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %ui128_237)
; CHECK: 00000000000000028000000000000002 0
  %si128_237 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %si128_237)
; CHECK: 00000000000000030000000000000000 0
  %ui128_238 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_238)
; CHECK: 00000000000000030000000000000000 0
  %si128_238 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_238)
; CHECK: 00000000000000030000000000000001 0
  %ui128_239 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_239)
; CHECK: 00000000000000030000000000000001 0
  %si128_239 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_239)
; CHECK: 00000000000000000000000000000002 1
  %ui128_240 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %ui128_240)
; CHECK: 00000000000000000000000000000002 0
  %si128_240 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %si128_240)
; CHECK: 00000000000000000000000000000003 1
  %ui128_241 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %ui128_241)
; CHECK: 00000000000000000000000000000003 0
  %si128_241 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %si128_241)
; CHECK: 00000000000000000000000000000004 1
  %ui128_242 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %ui128_242)
; CHECK: 00000000000000000000000000000004 0
  %si128_242 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %si128_242)
; CHECK: 00000000000000010000000000000001 1
  %ui128_243 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_243)
; CHECK: 00000000000000010000000000000001 0
  %si128_243 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_243)
; CHECK: 00000000000000010000000000000000 1
  %ui128_244 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_244)
; CHECK: 00000000000000010000000000000000 0
  %si128_244 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %si128_244)
; CHECK: 80000000000000010000000000000002 0
  %ui128_245 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_245)
; CHECK: 80000000000000010000000000000002 0
  %si128_245 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_245)
; CHECK: 40000000000000010000000000000002 0
  %ui128_246 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_246)
; CHECK: 40000000000000010000000000000002 0
  %si128_246 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_246)
; CHECK: 80000000000000010000000000000001 0
  %ui128_247 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_247)
; CHECK: 80000000000000010000000000000001 1
  %si128_247 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_247)
; CHECK: 7ffffffffffffff10000000000000002 0
  %ui128_248 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %ui128_248)
; CHECK: 7ffffffffffffff10000000000000002 0
  %si128_248 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %si128_248)
; CHECK: 7ffffffffffffff10000000000000003 0
  %ui128_249 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %ui128_249)
; CHECK: 7ffffffffffffff10000000000000003 0
  %si128_249 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %si128_249)
; CHECK: 40000000000000010000000000000001 0
  %ui128_250 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_250)
; CHECK: 40000000000000010000000000000001 0
  %si128_250 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000010000000000000002, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_250)
; CHECK: 00000000000000017fffffffffffffff 0
  %ui128_251 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_251)
; CHECK: 00000000000000017fffffffffffffff 0
  %si128_251 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_251)
; CHECK: 00000000000000018000000000000000 0
  %ui128_252 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %ui128_252)
; CHECK: 00000000000000018000000000000000 0
  %si128_252 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %si128_252)
; CHECK: 00000000000000018000000000000001 0
  %ui128_253 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %ui128_253)
; CHECK: 00000000000000018000000000000001 0
  %si128_253 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %si128_253)
; CHECK: 0000000000000001fffffffffffffffe 0
  %ui128_254 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_254)
; CHECK: 0000000000000001fffffffffffffffe 0
  %si128_254 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %si128_254)
; CHECK: 0000000000000001ffffffffffffffff 0
  %ui128_255 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %ui128_255)
; CHECK: 0000000000000001ffffffffffffffff 0
  %si128_255 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %si128_255)
; CHECK: 00000000000000027ffffffffffffffd 0
  %ui128_256 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_256)
; CHECK: 00000000000000027ffffffffffffffd 0
  %si128_256 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_256)
; CHECK: 00000000000000027ffffffffffffffe 0
  %ui128_257 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_257)
; CHECK: 00000000000000027ffffffffffffffe 0
  %si128_257 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_257)
; CHECK: 00000000000000027fffffffffffffff 0
  %ui128_258 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %ui128_258)
; CHECK: 00000000000000027fffffffffffffff 0
  %si128_258 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %si128_258)
; CHECK: 00000000000000028000000000000000 0
  %ui128_259 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %ui128_259)
; CHECK: 00000000000000028000000000000000 0
  %si128_259 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %si128_259)
; CHECK: 00000000000000028000000000000001 0
  %ui128_260 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %ui128_260)
; CHECK: 00000000000000028000000000000001 0
  %si128_260 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %si128_260)
; CHECK: 0000000000000002fffffffffffffffe 0
  %ui128_261 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_261)
; CHECK: 0000000000000002fffffffffffffffe 0
  %si128_261 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %si128_261)
; CHECK: 0000000000000002ffffffffffffffff 0
  %ui128_262 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %ui128_262)
; CHECK: 0000000000000002ffffffffffffffff 0
  %si128_262 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %si128_262)
; CHECK: 00000000000000037ffffffffffffffd 0
  %ui128_263 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_263)
; CHECK: 00000000000000037ffffffffffffffd 0
  %si128_263 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_263)
; CHECK: 00000000000000037ffffffffffffffe 0
  %ui128_264 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_264)
; CHECK: 00000000000000037ffffffffffffffe 0
  %si128_264 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_264)
; CHECK: 00000000000000007fffffffffffffff 1
  %ui128_265 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %ui128_265)
; CHECK: 00000000000000007fffffffffffffff 0
  %si128_265 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %si128_265)
; CHECK: 00000000000000008000000000000000 1
  %ui128_266 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %ui128_266)
; CHECK: 00000000000000008000000000000000 0
  %si128_266 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %si128_266)
; CHECK: 00000000000000008000000000000001 1
  %ui128_267 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %ui128_267)
; CHECK: 00000000000000008000000000000001 0
  %si128_267 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %si128_267)
; CHECK: 00000000000000017ffffffffffffffe 1
  %ui128_268 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_268)
; CHECK: 00000000000000017ffffffffffffffe 0
  %si128_268 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_268)
; CHECK: 00000000000000017ffffffffffffffd 1
  %ui128_269 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_269)
; CHECK: 00000000000000017ffffffffffffffd 0
  %si128_269 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %si128_269)
; CHECK: 80000000000000017fffffffffffffff 0
  %ui128_270 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_270)
; CHECK: 80000000000000017fffffffffffffff 0
  %si128_270 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_270)
; CHECK: 40000000000000017fffffffffffffff 0
  %ui128_271 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_271)
; CHECK: 40000000000000017fffffffffffffff 0
  %si128_271 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_271)
; CHECK: 80000000000000017ffffffffffffffe 0
  %ui128_272 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_272)
; CHECK: 80000000000000017ffffffffffffffe 1
  %si128_272 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_272)
; CHECK: 7ffffffffffffff17fffffffffffffff 0
  %ui128_273 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %ui128_273)
; CHECK: 7ffffffffffffff17fffffffffffffff 0
  %si128_273 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %si128_273)
; CHECK: 7ffffffffffffff18000000000000000 0
  %ui128_274 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %ui128_274)
; CHECK: 7ffffffffffffff18000000000000000 0
  %si128_274 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %si128_274)
; CHECK: 40000000000000017ffffffffffffffe 0
  %ui128_275 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_275)
; CHECK: 40000000000000017ffffffffffffffe 0
  %si128_275 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000017fffffffffffffff, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_275)
; CHECK: 00000000000000018000000000000000 0
  %ui128_276 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_276)
; CHECK: 00000000000000018000000000000000 0
  %si128_276 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_276)
; CHECK: 00000000000000018000000000000001 0
  %ui128_277 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %ui128_277)
; CHECK: 00000000000000018000000000000001 0
  %si128_277 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %si128_277)
; CHECK: 00000000000000018000000000000002 0
  %ui128_278 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %ui128_278)
; CHECK: 00000000000000018000000000000002 0
  %si128_278 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %si128_278)
; CHECK: 0000000000000001ffffffffffffffff 0
  %ui128_279 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_279)
; CHECK: 0000000000000001ffffffffffffffff 0
  %si128_279 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %si128_279)
; CHECK: 00000000000000020000000000000000 0
  %ui128_280 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %ui128_280)
; CHECK: 00000000000000020000000000000000 0
  %si128_280 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %si128_280)
; CHECK: 00000000000000027ffffffffffffffe 0
  %ui128_281 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_281)
; CHECK: 00000000000000027ffffffffffffffe 0
  %si128_281 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_281)
; CHECK: 00000000000000027fffffffffffffff 0
  %ui128_282 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_282)
; CHECK: 00000000000000027fffffffffffffff 0
  %si128_282 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_282)
; CHECK: 00000000000000028000000000000000 0
  %ui128_283 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %ui128_283)
; CHECK: 00000000000000028000000000000000 0
  %si128_283 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %si128_283)
; CHECK: 00000000000000028000000000000001 0
  %ui128_284 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %ui128_284)
; CHECK: 00000000000000028000000000000001 0
  %si128_284 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %si128_284)
; CHECK: 00000000000000028000000000000002 0
  %ui128_285 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %ui128_285)
; CHECK: 00000000000000028000000000000002 0
  %si128_285 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %si128_285)
; CHECK: 0000000000000002ffffffffffffffff 0
  %ui128_286 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_286)
; CHECK: 0000000000000002ffffffffffffffff 0
  %si128_286 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %si128_286)
; CHECK: 00000000000000030000000000000000 0
  %ui128_287 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %ui128_287)
; CHECK: 00000000000000030000000000000000 0
  %si128_287 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %si128_287)
; CHECK: 00000000000000037ffffffffffffffe 0
  %ui128_288 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_288)
; CHECK: 00000000000000037ffffffffffffffe 0
  %si128_288 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_288)
; CHECK: 00000000000000037fffffffffffffff 0
  %ui128_289 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_289)
; CHECK: 00000000000000037fffffffffffffff 0
  %si128_289 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_289)
; CHECK: 00000000000000008000000000000000 1
  %ui128_290 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %ui128_290)
; CHECK: 00000000000000008000000000000000 0
  %si128_290 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %si128_290)
; CHECK: 00000000000000008000000000000001 1
  %ui128_291 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %ui128_291)
; CHECK: 00000000000000008000000000000001 0
  %si128_291 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %si128_291)
; CHECK: 00000000000000008000000000000002 1
  %ui128_292 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %ui128_292)
; CHECK: 00000000000000008000000000000002 0
  %si128_292 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %si128_292)
; CHECK: 00000000000000017fffffffffffffff 1
  %ui128_293 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_293)
; CHECK: 00000000000000017fffffffffffffff 0
  %si128_293 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_293)
; CHECK: 00000000000000017ffffffffffffffe 1
  %ui128_294 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_294)
; CHECK: 00000000000000017ffffffffffffffe 0
  %si128_294 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %si128_294)
; CHECK: 80000000000000018000000000000000 0
  %ui128_295 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_295)
; CHECK: 80000000000000018000000000000000 0
  %si128_295 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_295)
; CHECK: 40000000000000018000000000000000 0
  %ui128_296 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_296)
; CHECK: 40000000000000018000000000000000 0
  %si128_296 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_296)
; CHECK: 80000000000000017fffffffffffffff 0
  %ui128_297 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_297)
; CHECK: 80000000000000017fffffffffffffff 1
  %si128_297 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_297)
; CHECK: 7ffffffffffffff18000000000000000 0
  %ui128_298 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %ui128_298)
; CHECK: 7ffffffffffffff18000000000000000 0
  %si128_298 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %si128_298)
; CHECK: 7ffffffffffffff18000000000000001 0
  %ui128_299 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %ui128_299)
; CHECK: 7ffffffffffffff18000000000000001 0
  %si128_299 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %si128_299)
; CHECK: 40000000000000017fffffffffffffff 0
  %ui128_300 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_300)
; CHECK: 40000000000000017fffffffffffffff 0
  %si128_300 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x00000000000000018000000000000000, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_300)
; CHECK: 0000000000000001fffffffffffffffe 0
  %ui128_301 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_301)
; CHECK: 0000000000000001fffffffffffffffe 0
  %si128_301 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_301)
; CHECK: 0000000000000001ffffffffffffffff 0
  %ui128_302 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %ui128_302)
; CHECK: 0000000000000001ffffffffffffffff 0
  %si128_302 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %si128_302)
; CHECK: 00000000000000020000000000000000 0
  %ui128_303 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %ui128_303)
; CHECK: 00000000000000020000000000000000 0
  %si128_303 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %si128_303)
; CHECK: 00000000000000027ffffffffffffffd 0
  %ui128_304 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_304)
; CHECK: 00000000000000027ffffffffffffffd 0
  %si128_304 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %si128_304)
; CHECK: 00000000000000027ffffffffffffffe 0
  %ui128_305 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %ui128_305)
; CHECK: 00000000000000027ffffffffffffffe 0
  %si128_305 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %si128_305)
; CHECK: 0000000000000002fffffffffffffffc 0
  %ui128_306 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_306)
; CHECK: 0000000000000002fffffffffffffffc 0
  %si128_306 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_306)
; CHECK: 0000000000000002fffffffffffffffd 0
  %ui128_307 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_307)
; CHECK: 0000000000000002fffffffffffffffd 0
  %si128_307 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_307)
; CHECK: 0000000000000002fffffffffffffffe 0
  %ui128_308 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %ui128_308)
; CHECK: 0000000000000002fffffffffffffffe 0
  %si128_308 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %si128_308)
; CHECK: 0000000000000002ffffffffffffffff 0
  %ui128_309 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %ui128_309)
; CHECK: 0000000000000002ffffffffffffffff 0
  %si128_309 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %si128_309)
; CHECK: 00000000000000030000000000000000 0
  %ui128_310 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %ui128_310)
; CHECK: 00000000000000030000000000000000 0
  %si128_310 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %si128_310)
; CHECK: 00000000000000037ffffffffffffffd 0
  %ui128_311 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_311)
; CHECK: 00000000000000037ffffffffffffffd 0
  %si128_311 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %si128_311)
; CHECK: 00000000000000037ffffffffffffffe 0
  %ui128_312 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %ui128_312)
; CHECK: 00000000000000037ffffffffffffffe 0
  %si128_312 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %si128_312)
; CHECK: 0000000000000003fffffffffffffffc 0
  %ui128_313 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_313)
; CHECK: 0000000000000003fffffffffffffffc 0
  %si128_313 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_313)
; CHECK: 0000000000000003fffffffffffffffd 0
  %ui128_314 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_314)
; CHECK: 0000000000000003fffffffffffffffd 0
  %si128_314 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_314)
; CHECK: 0000000000000000fffffffffffffffe 1
  %ui128_315 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %ui128_315)
; CHECK: 0000000000000000fffffffffffffffe 0
  %si128_315 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %si128_315)
; CHECK: 0000000000000000ffffffffffffffff 1
  %ui128_316 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %ui128_316)
; CHECK: 0000000000000000ffffffffffffffff 0
  %si128_316 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %si128_316)
; CHECK: 00000000000000010000000000000000 1
  %ui128_317 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %ui128_317)
; CHECK: 00000000000000010000000000000000 0
  %si128_317 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %si128_317)
; CHECK: 0000000000000001fffffffffffffffd 1
  %ui128_318 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_318)
; CHECK: 0000000000000001fffffffffffffffd 0
  %si128_318 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_318)
; CHECK: 0000000000000001fffffffffffffffc 1
  %ui128_319 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_319)
; CHECK: 0000000000000001fffffffffffffffc 0
  %si128_319 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %si128_319)
; CHECK: 8000000000000001fffffffffffffffe 0
  %ui128_320 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_320)
; CHECK: 8000000000000001fffffffffffffffe 0
  %si128_320 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_320)
; CHECK: 4000000000000001fffffffffffffffe 0
  %ui128_321 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_321)
; CHECK: 4000000000000001fffffffffffffffe 0
  %si128_321 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_321)
; CHECK: 8000000000000001fffffffffffffffd 0
  %ui128_322 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_322)
; CHECK: 8000000000000001fffffffffffffffd 1
  %si128_322 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_322)
; CHECK: 7ffffffffffffff1fffffffffffffffe 0
  %ui128_323 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %ui128_323)
; CHECK: 7ffffffffffffff1fffffffffffffffe 0
  %si128_323 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %si128_323)
; CHECK: 7ffffffffffffff1ffffffffffffffff 0
  %ui128_324 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %ui128_324)
; CHECK: 7ffffffffffffff1ffffffffffffffff 0
  %si128_324 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %si128_324)
; CHECK: 4000000000000001fffffffffffffffd 0
  %ui128_325 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_325)
; CHECK: 4000000000000001fffffffffffffffd 0
  %si128_325 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001fffffffffffffffe, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_325)
; CHECK: 0000000000000001ffffffffffffffff 0
  %ui128_326 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_326)
; CHECK: 0000000000000001ffffffffffffffff 0
  %si128_326 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_326)
; CHECK: 00000000000000020000000000000000 0
  %ui128_327 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %ui128_327)
; CHECK: 00000000000000020000000000000000 0
  %si128_327 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %si128_327)
; CHECK: 00000000000000020000000000000001 0
  %ui128_328 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %ui128_328)
; CHECK: 00000000000000020000000000000001 0
  %si128_328 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %si128_328)
; CHECK: 00000000000000027ffffffffffffffe 0
  %ui128_329 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_329)
; CHECK: 00000000000000027ffffffffffffffe 0
  %si128_329 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %si128_329)
; CHECK: 00000000000000027fffffffffffffff 0
  %ui128_330 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %ui128_330)
; CHECK: 00000000000000027fffffffffffffff 0
  %si128_330 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %si128_330)
; CHECK: 0000000000000002fffffffffffffffd 0
  %ui128_331 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_331)
; CHECK: 0000000000000002fffffffffffffffd 0
  %si128_331 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_331)
; CHECK: 0000000000000002fffffffffffffffe 0
  %ui128_332 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_332)
; CHECK: 0000000000000002fffffffffffffffe 0
  %si128_332 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_332)
; CHECK: 0000000000000002ffffffffffffffff 0
  %ui128_333 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %ui128_333)
; CHECK: 0000000000000002ffffffffffffffff 0
  %si128_333 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %si128_333)
; CHECK: 00000000000000030000000000000000 0
  %ui128_334 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %ui128_334)
; CHECK: 00000000000000030000000000000000 0
  %si128_334 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %si128_334)
; CHECK: 00000000000000030000000000000001 0
  %ui128_335 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %ui128_335)
; CHECK: 00000000000000030000000000000001 0
  %si128_335 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %si128_335)
; CHECK: 00000000000000037ffffffffffffffe 0
  %ui128_336 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_336)
; CHECK: 00000000000000037ffffffffffffffe 0
  %si128_336 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %si128_336)
; CHECK: 00000000000000037fffffffffffffff 0
  %ui128_337 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %ui128_337)
; CHECK: 00000000000000037fffffffffffffff 0
  %si128_337 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %si128_337)
; CHECK: 0000000000000003fffffffffffffffd 0
  %ui128_338 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_338)
; CHECK: 0000000000000003fffffffffffffffd 0
  %si128_338 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_338)
; CHECK: 0000000000000003fffffffffffffffe 0
  %ui128_339 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_339)
; CHECK: 0000000000000003fffffffffffffffe 0
  %si128_339 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_339)
; CHECK: 0000000000000000ffffffffffffffff 1
  %ui128_340 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %ui128_340)
; CHECK: 0000000000000000ffffffffffffffff 0
  %si128_340 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %si128_340)
; CHECK: 00000000000000010000000000000000 1
  %ui128_341 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %ui128_341)
; CHECK: 00000000000000010000000000000000 0
  %si128_341 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %si128_341)
; CHECK: 00000000000000010000000000000001 1
  %ui128_342 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %ui128_342)
; CHECK: 00000000000000010000000000000001 0
  %si128_342 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %si128_342)
; CHECK: 0000000000000001fffffffffffffffe 1
  %ui128_343 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_343)
; CHECK: 0000000000000001fffffffffffffffe 0
  %si128_343 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_343)
; CHECK: 0000000000000001fffffffffffffffd 1
  %ui128_344 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_344)
; CHECK: 0000000000000001fffffffffffffffd 0
  %si128_344 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %si128_344)
; CHECK: 8000000000000001ffffffffffffffff 0
  %ui128_345 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_345)
; CHECK: 8000000000000001ffffffffffffffff 0
  %si128_345 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_345)
; CHECK: 4000000000000001ffffffffffffffff 0
  %ui128_346 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_346)
; CHECK: 4000000000000001ffffffffffffffff 0
  %si128_346 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_346)
; CHECK: 8000000000000001fffffffffffffffe 0
  %ui128_347 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_347)
; CHECK: 8000000000000001fffffffffffffffe 1
  %si128_347 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_347)
; CHECK: 7ffffffffffffff1ffffffffffffffff 0
  %ui128_348 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %ui128_348)
; CHECK: 7ffffffffffffff1ffffffffffffffff 0
  %si128_348 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %si128_348)
; CHECK: 7ffffffffffffff20000000000000000 0
  %ui128_349 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %ui128_349)
; CHECK: 7ffffffffffffff20000000000000000 0
  %si128_349 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %si128_349)
; CHECK: 4000000000000001fffffffffffffffe 0
  %ui128_350 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_350)
; CHECK: 4000000000000001fffffffffffffffe 0
  %si128_350 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x0000000000000001ffffffffffffffff, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_350)
; CHECK: ffffffffffffffff0000000000000000 0
  %ui128_351 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_351)
; CHECK: ffffffffffffffff0000000000000000 0
  %si128_351 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_351)
; CHECK: ffffffffffffffff0000000000000001 0
  %ui128_352 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %ui128_352)
; CHECK: ffffffffffffffff0000000000000001 0
  %si128_352 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %si128_352)
; CHECK: ffffffffffffffff0000000000000002 0
  %ui128_353 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %ui128_353)
; CHECK: ffffffffffffffff0000000000000002 0
  %si128_353 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %si128_353)
; CHECK: ffffffffffffffff7fffffffffffffff 0
  %ui128_354 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_354)
; CHECK: ffffffffffffffff7fffffffffffffff 0
  %si128_354 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %si128_354)
; CHECK: ffffffffffffffff8000000000000000 0
  %ui128_355 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %ui128_355)
; CHECK: ffffffffffffffff8000000000000000 0
  %si128_355 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %si128_355)
; CHECK: fffffffffffffffffffffffffffffffe 0
  %ui128_356 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_356)
; CHECK: fffffffffffffffffffffffffffffffe 0
  %si128_356 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_356)
; CHECK: ffffffffffffffffffffffffffffffff 0
  %ui128_357 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_357)
; CHECK: ffffffffffffffffffffffffffffffff 0
  %si128_357 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_357)
; CHECK: 00000000000000000000000000000000 1
  %ui128_358 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %ui128_358)
; CHECK: 00000000000000000000000000000000 0
  %si128_358 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %si128_358)
; CHECK: 00000000000000000000000000000001 1
  %ui128_359 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %ui128_359)
; CHECK: 00000000000000000000000000000001 0
  %si128_359 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %si128_359)
; CHECK: 00000000000000000000000000000002 1
  %ui128_360 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %ui128_360)
; CHECK: 00000000000000000000000000000002 0
  %si128_360 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %si128_360)
; CHECK: 00000000000000007fffffffffffffff 1
  %ui128_361 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_361)
; CHECK: 00000000000000007fffffffffffffff 0
  %si128_361 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %si128_361)
; CHECK: 00000000000000008000000000000000 1
  %ui128_362 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %ui128_362)
; CHECK: 00000000000000008000000000000000 0
  %si128_362 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %si128_362)
; CHECK: 0000000000000000fffffffffffffffe 1
  %ui128_363 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_363)
; CHECK: 0000000000000000fffffffffffffffe 0
  %si128_363 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_363)
; CHECK: 0000000000000000ffffffffffffffff 1
  %ui128_364 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_364)
; CHECK: 0000000000000000ffffffffffffffff 0
  %si128_364 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_364)
; CHECK: fffffffffffffffe0000000000000000 1
  %ui128_365 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %ui128_365)
; CHECK: fffffffffffffffe0000000000000000 0
  %si128_365 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %si128_365)
; CHECK: fffffffffffffffe0000000000000001 1
  %ui128_366 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %ui128_366)
; CHECK: fffffffffffffffe0000000000000001 0
  %si128_366 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %si128_366)
; CHECK: fffffffffffffffe0000000000000002 1
  %ui128_367 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %ui128_367)
; CHECK: fffffffffffffffe0000000000000002 0
  %si128_367 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %si128_367)
; CHECK: fffffffffffffffeffffffffffffffff 1
  %ui128_368 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_368)
; CHECK: fffffffffffffffeffffffffffffffff 0
  %si128_368 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_368)
; CHECK: fffffffffffffffefffffffffffffffe 1
  %ui128_369 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_369)
; CHECK: fffffffffffffffefffffffffffffffe 0
  %si128_369 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %si128_369)
; CHECK: 7fffffffffffffff0000000000000000 1
  %ui128_370 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_370)
; CHECK: 7fffffffffffffff0000000000000000 1
  %si128_370 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_370)
; CHECK: 3fffffffffffffff0000000000000000 1
  %ui128_371 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_371)
; CHECK: 3fffffffffffffff0000000000000000 0
  %si128_371 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_371)
; CHECK: 7ffffffffffffffeffffffffffffffff 1
  %ui128_372 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_372)
; CHECK: 7ffffffffffffffeffffffffffffffff 0
  %si128_372 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_372)
; CHECK: 7fffffffffffffef0000000000000000 1
  %ui128_373 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %ui128_373)
; CHECK: 7fffffffffffffef0000000000000000 0
  %si128_373 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %si128_373)
; CHECK: 7fffffffffffffef0000000000000001 1
  %ui128_374 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %ui128_374)
; CHECK: 7fffffffffffffef0000000000000001 0
  %si128_374 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %si128_374)
; CHECK: 3ffffffffffffffeffffffffffffffff 1
  %ui128_375 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_375)
; CHECK: 3ffffffffffffffeffffffffffffffff 0
  %si128_375 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000000, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_375)
; CHECK: ffffffffffffffff0000000000000001 0
  %ui128_376 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_376)
; CHECK: ffffffffffffffff0000000000000001 0
  %si128_376 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_376)
; CHECK: ffffffffffffffff0000000000000002 0
  %ui128_377 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %ui128_377)
; CHECK: ffffffffffffffff0000000000000002 0
  %si128_377 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %si128_377)
; CHECK: ffffffffffffffff0000000000000003 0
  %ui128_378 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %ui128_378)
; CHECK: ffffffffffffffff0000000000000003 0
  %si128_378 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %si128_378)
; CHECK: ffffffffffffffff8000000000000000 0
  %ui128_379 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_379)
; CHECK: ffffffffffffffff8000000000000000 0
  %si128_379 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %si128_379)
; CHECK: ffffffffffffffff8000000000000001 0
  %ui128_380 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %ui128_380)
; CHECK: ffffffffffffffff8000000000000001 0
  %si128_380 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %si128_380)
; CHECK: ffffffffffffffffffffffffffffffff 0
  %ui128_381 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_381)
; CHECK: ffffffffffffffffffffffffffffffff 0
  %si128_381 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_381)
; CHECK: 00000000000000000000000000000000 1
  %ui128_382 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_382)
; CHECK: 00000000000000000000000000000000 0
  %si128_382 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_382)
; CHECK: 00000000000000000000000000000001 1
  %ui128_383 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %ui128_383)
; CHECK: 00000000000000000000000000000001 0
  %si128_383 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %si128_383)
; CHECK: 00000000000000000000000000000002 1
  %ui128_384 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %ui128_384)
; CHECK: 00000000000000000000000000000002 0
  %si128_384 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %si128_384)
; CHECK: 00000000000000000000000000000003 1
  %ui128_385 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %ui128_385)
; CHECK: 00000000000000000000000000000003 0
  %si128_385 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %si128_385)
; CHECK: 00000000000000008000000000000000 1
  %ui128_386 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_386)
; CHECK: 00000000000000008000000000000000 0
  %si128_386 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %si128_386)
; CHECK: 00000000000000008000000000000001 1
  %ui128_387 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %ui128_387)
; CHECK: 00000000000000008000000000000001 0
  %si128_387 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %si128_387)
; CHECK: 0000000000000000ffffffffffffffff 1
  %ui128_388 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_388)
; CHECK: 0000000000000000ffffffffffffffff 0
  %si128_388 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_388)
; CHECK: 00000000000000010000000000000000 1
  %ui128_389 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_389)
; CHECK: 00000000000000010000000000000000 0
  %si128_389 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_389)
; CHECK: fffffffffffffffe0000000000000001 1
  %ui128_390 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %ui128_390)
; CHECK: fffffffffffffffe0000000000000001 0
  %si128_390 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %si128_390)
; CHECK: fffffffffffffffe0000000000000002 1
  %ui128_391 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %ui128_391)
; CHECK: fffffffffffffffe0000000000000002 0
  %si128_391 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %si128_391)
; CHECK: fffffffffffffffe0000000000000003 1
  %ui128_392 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %ui128_392)
; CHECK: fffffffffffffffe0000000000000003 0
  %si128_392 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %si128_392)
; CHECK: ffffffffffffffff0000000000000000 1
  %ui128_393 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_393)
; CHECK: ffffffffffffffff0000000000000000 0
  %si128_393 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_393)
; CHECK: fffffffffffffffeffffffffffffffff 1
  %ui128_394 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_394)
; CHECK: fffffffffffffffeffffffffffffffff 0
  %si128_394 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %si128_394)
; CHECK: 7fffffffffffffff0000000000000001 1
  %ui128_395 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_395)
; CHECK: 7fffffffffffffff0000000000000001 1
  %si128_395 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_395)
; CHECK: 3fffffffffffffff0000000000000001 1
  %ui128_396 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_396)
; CHECK: 3fffffffffffffff0000000000000001 0
  %si128_396 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_396)
; CHECK: 7fffffffffffffff0000000000000000 1
  %ui128_397 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_397)
; CHECK: 7fffffffffffffff0000000000000000 0
  %si128_397 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_397)
; CHECK: 7fffffffffffffef0000000000000001 1
  %ui128_398 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %ui128_398)
; CHECK: 7fffffffffffffef0000000000000001 0
  %si128_398 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %si128_398)
; CHECK: 7fffffffffffffef0000000000000002 1
  %ui128_399 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %ui128_399)
; CHECK: 7fffffffffffffef0000000000000002 0
  %si128_399 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %si128_399)
; CHECK: 3fffffffffffffff0000000000000000 1
  %ui128_400 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_400)
; CHECK: 3fffffffffffffff0000000000000000 0
  %si128_400 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000001, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_400)
; CHECK: ffffffffffffffff0000000000000002 0
  %ui128_401 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_401)
; CHECK: ffffffffffffffff0000000000000002 0
  %si128_401 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_401)
; CHECK: ffffffffffffffff0000000000000003 0
  %ui128_402 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %ui128_402)
; CHECK: ffffffffffffffff0000000000000003 0
  %si128_402 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %si128_402)
; CHECK: ffffffffffffffff0000000000000004 0
  %ui128_403 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %ui128_403)
; CHECK: ffffffffffffffff0000000000000004 0
  %si128_403 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %si128_403)
; CHECK: ffffffffffffffff8000000000000001 0
  %ui128_404 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_404)
; CHECK: ffffffffffffffff8000000000000001 0
  %si128_404 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %si128_404)
; CHECK: ffffffffffffffff8000000000000002 0
  %ui128_405 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %ui128_405)
; CHECK: ffffffffffffffff8000000000000002 0
  %si128_405 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %si128_405)
; CHECK: 00000000000000000000000000000000 1
  %ui128_406 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_406)
; CHECK: 00000000000000000000000000000000 0
  %si128_406 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_406)
; CHECK: 00000000000000000000000000000001 1
  %ui128_407 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_407)
; CHECK: 00000000000000000000000000000001 0
  %si128_407 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_407)
; CHECK: 00000000000000000000000000000002 1
  %ui128_408 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %ui128_408)
; CHECK: 00000000000000000000000000000002 0
  %si128_408 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %si128_408)
; CHECK: 00000000000000000000000000000003 1
  %ui128_409 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %ui128_409)
; CHECK: 00000000000000000000000000000003 0
  %si128_409 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %si128_409)
; CHECK: 00000000000000000000000000000004 1
  %ui128_410 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %ui128_410)
; CHECK: 00000000000000000000000000000004 0
  %si128_410 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %si128_410)
; CHECK: 00000000000000008000000000000001 1
  %ui128_411 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_411)
; CHECK: 00000000000000008000000000000001 0
  %si128_411 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %si128_411)
; CHECK: 00000000000000008000000000000002 1
  %ui128_412 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %ui128_412)
; CHECK: 00000000000000008000000000000002 0
  %si128_412 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %si128_412)
; CHECK: 00000000000000010000000000000000 1
  %ui128_413 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_413)
; CHECK: 00000000000000010000000000000000 0
  %si128_413 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_413)
; CHECK: 00000000000000010000000000000001 1
  %ui128_414 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_414)
; CHECK: 00000000000000010000000000000001 0
  %si128_414 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_414)
; CHECK: fffffffffffffffe0000000000000002 1
  %ui128_415 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %ui128_415)
; CHECK: fffffffffffffffe0000000000000002 0
  %si128_415 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %si128_415)
; CHECK: fffffffffffffffe0000000000000003 1
  %ui128_416 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %ui128_416)
; CHECK: fffffffffffffffe0000000000000003 0
  %si128_416 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %si128_416)
; CHECK: fffffffffffffffe0000000000000004 1
  %ui128_417 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %ui128_417)
; CHECK: fffffffffffffffe0000000000000004 0
  %si128_417 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %si128_417)
; CHECK: ffffffffffffffff0000000000000001 1
  %ui128_418 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_418)
; CHECK: ffffffffffffffff0000000000000001 0
  %si128_418 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_418)
; CHECK: ffffffffffffffff0000000000000000 1
  %ui128_419 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_419)
; CHECK: ffffffffffffffff0000000000000000 0
  %si128_419 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %si128_419)
; CHECK: 7fffffffffffffff0000000000000002 1
  %ui128_420 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_420)
; CHECK: 7fffffffffffffff0000000000000002 1
  %si128_420 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_420)
; CHECK: 3fffffffffffffff0000000000000002 1
  %ui128_421 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_421)
; CHECK: 3fffffffffffffff0000000000000002 0
  %si128_421 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_421)
; CHECK: 7fffffffffffffff0000000000000001 1
  %ui128_422 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_422)
; CHECK: 7fffffffffffffff0000000000000001 0
  %si128_422 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_422)
; CHECK: 7fffffffffffffef0000000000000002 1
  %ui128_423 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %ui128_423)
; CHECK: 7fffffffffffffef0000000000000002 0
  %si128_423 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %si128_423)
; CHECK: 7fffffffffffffef0000000000000003 1
  %ui128_424 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %ui128_424)
; CHECK: 7fffffffffffffef0000000000000003 0
  %si128_424 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %si128_424)
; CHECK: 3fffffffffffffff0000000000000001 1
  %ui128_425 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_425)
; CHECK: 3fffffffffffffff0000000000000001 0
  %si128_425 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffff0000000000000002, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_425)
; CHECK: ffffffffffffffffffffffffffffffff 0
  %ui128_426 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_426)
; CHECK: ffffffffffffffffffffffffffffffff 0
  %si128_426 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_426)
; CHECK: 00000000000000000000000000000000 1
  %ui128_427 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %ui128_427)
; CHECK: 00000000000000000000000000000000 0
  %si128_427 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %si128_427)
; CHECK: 00000000000000000000000000000001 1
  %ui128_428 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %ui128_428)
; CHECK: 00000000000000000000000000000001 0
  %si128_428 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %si128_428)
; CHECK: 00000000000000007ffffffffffffffe 1
  %ui128_429 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_429)
; CHECK: 00000000000000007ffffffffffffffe 0
  %si128_429 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %si128_429)
; CHECK: 00000000000000007fffffffffffffff 1
  %ui128_430 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %ui128_430)
; CHECK: 00000000000000007fffffffffffffff 0
  %si128_430 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %si128_430)
; CHECK: 0000000000000000fffffffffffffffd 1
  %ui128_431 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_431)
; CHECK: 0000000000000000fffffffffffffffd 0
  %si128_431 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_431)
; CHECK: 0000000000000000fffffffffffffffe 1
  %ui128_432 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_432)
; CHECK: 0000000000000000fffffffffffffffe 0
  %si128_432 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_432)
; CHECK: 0000000000000000ffffffffffffffff 1
  %ui128_433 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %ui128_433)
; CHECK: 0000000000000000ffffffffffffffff 0
  %si128_433 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %si128_433)
; CHECK: 00000000000000010000000000000000 1
  %ui128_434 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %ui128_434)
; CHECK: 00000000000000010000000000000000 0
  %si128_434 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %si128_434)
; CHECK: 00000000000000010000000000000001 1
  %ui128_435 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %ui128_435)
; CHECK: 00000000000000010000000000000001 0
  %si128_435 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %si128_435)
; CHECK: 00000000000000017ffffffffffffffe 1
  %ui128_436 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_436)
; CHECK: 00000000000000017ffffffffffffffe 0
  %si128_436 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %si128_436)
; CHECK: 00000000000000017fffffffffffffff 1
  %ui128_437 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %ui128_437)
; CHECK: 00000000000000017fffffffffffffff 0
  %si128_437 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %si128_437)
; CHECK: 0000000000000001fffffffffffffffd 1
  %ui128_438 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_438)
; CHECK: 0000000000000001fffffffffffffffd 0
  %si128_438 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_438)
; CHECK: 0000000000000001fffffffffffffffe 1
  %ui128_439 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_439)
; CHECK: 0000000000000001fffffffffffffffe 0
  %si128_439 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_439)
; CHECK: fffffffffffffffeffffffffffffffff 1
  %ui128_440 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %ui128_440)
; CHECK: fffffffffffffffeffffffffffffffff 0
  %si128_440 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %si128_440)
; CHECK: ffffffffffffffff0000000000000000 1
  %ui128_441 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %ui128_441)
; CHECK: ffffffffffffffff0000000000000000 0
  %si128_441 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %si128_441)
; CHECK: ffffffffffffffff0000000000000001 1
  %ui128_442 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %ui128_442)
; CHECK: ffffffffffffffff0000000000000001 0
  %si128_442 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %si128_442)
; CHECK: fffffffffffffffffffffffffffffffe 1
  %ui128_443 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_443)
; CHECK: fffffffffffffffffffffffffffffffe 0
  %si128_443 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_443)
; CHECK: fffffffffffffffffffffffffffffffd 1
  %ui128_444 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_444)
; CHECK: fffffffffffffffffffffffffffffffd 0
  %si128_444 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %si128_444)
; CHECK: 7fffffffffffffffffffffffffffffff 1
  %ui128_445 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_445)
; CHECK: 7fffffffffffffffffffffffffffffff 1
  %si128_445 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_445)
; CHECK: 3fffffffffffffffffffffffffffffff 1
  %ui128_446 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_446)
; CHECK: 3fffffffffffffffffffffffffffffff 0
  %si128_446 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_446)
; CHECK: 7ffffffffffffffffffffffffffffffe 1
  %ui128_447 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_447)
; CHECK: 7ffffffffffffffffffffffffffffffe 0
  %si128_447 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_447)
; CHECK: 7fffffffffffffefffffffffffffffff 1
  %ui128_448 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %ui128_448)
; CHECK: 7fffffffffffffefffffffffffffffff 0
  %si128_448 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %si128_448)
; CHECK: 7ffffffffffffff00000000000000000 1
  %ui128_449 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %ui128_449)
; CHECK: 7ffffffffffffff00000000000000000 0
  %si128_449 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %si128_449)
; CHECK: 3ffffffffffffffffffffffffffffffe 1
  %ui128_450 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_450)
; CHECK: 3ffffffffffffffffffffffffffffffe 0
  %si128_450 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xffffffffffffffffffffffffffffffff, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_450)
; CHECK: fffffffffffffffffffffffffffffffe 0
  %ui128_451 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_451)
; CHECK: fffffffffffffffffffffffffffffffe 0
  %si128_451 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_451)
; CHECK: ffffffffffffffffffffffffffffffff 0
  %ui128_452 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %ui128_452)
; CHECK: ffffffffffffffffffffffffffffffff 0
  %si128_452 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %si128_452)
; CHECK: 00000000000000000000000000000000 1
  %ui128_453 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %ui128_453)
; CHECK: 00000000000000000000000000000000 0
  %si128_453 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %si128_453)
; CHECK: 00000000000000007ffffffffffffffd 1
  %ui128_454 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_454)
; CHECK: 00000000000000007ffffffffffffffd 0
  %si128_454 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %si128_454)
; CHECK: 00000000000000007ffffffffffffffe 1
  %ui128_455 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %ui128_455)
; CHECK: 00000000000000007ffffffffffffffe 0
  %si128_455 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %si128_455)
; CHECK: 0000000000000000fffffffffffffffc 1
  %ui128_456 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_456)
; CHECK: 0000000000000000fffffffffffffffc 0
  %si128_456 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_456)
; CHECK: 0000000000000000fffffffffffffffd 1
  %ui128_457 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_457)
; CHECK: 0000000000000000fffffffffffffffd 0
  %si128_457 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_457)
; CHECK: 0000000000000000fffffffffffffffe 1
  %ui128_458 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %ui128_458)
; CHECK: 0000000000000000fffffffffffffffe 0
  %si128_458 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %si128_458)
; CHECK: 0000000000000000ffffffffffffffff 1
  %ui128_459 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %ui128_459)
; CHECK: 0000000000000000ffffffffffffffff 0
  %si128_459 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %si128_459)
; CHECK: 00000000000000010000000000000000 1
  %ui128_460 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %ui128_460)
; CHECK: 00000000000000010000000000000000 0
  %si128_460 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %si128_460)
; CHECK: 00000000000000017ffffffffffffffd 1
  %ui128_461 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_461)
; CHECK: 00000000000000017ffffffffffffffd 0
  %si128_461 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %si128_461)
; CHECK: 00000000000000017ffffffffffffffe 1
  %ui128_462 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %ui128_462)
; CHECK: 00000000000000017ffffffffffffffe 0
  %si128_462 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %si128_462)
; CHECK: 0000000000000001fffffffffffffffc 1
  %ui128_463 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_463)
; CHECK: 0000000000000001fffffffffffffffc 0
  %si128_463 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_463)
; CHECK: 0000000000000001fffffffffffffffd 1
  %ui128_464 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_464)
; CHECK: 0000000000000001fffffffffffffffd 0
  %si128_464 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_464)
; CHECK: fffffffffffffffefffffffffffffffe 1
  %ui128_465 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %ui128_465)
; CHECK: fffffffffffffffefffffffffffffffe 0
  %si128_465 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %si128_465)
; CHECK: fffffffffffffffeffffffffffffffff 1
  %ui128_466 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %ui128_466)
; CHECK: fffffffffffffffeffffffffffffffff 0
  %si128_466 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %si128_466)
; CHECK: ffffffffffffffff0000000000000000 1
  %ui128_467 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %ui128_467)
; CHECK: ffffffffffffffff0000000000000000 0
  %si128_467 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %si128_467)
; CHECK: fffffffffffffffffffffffffffffffd 1
  %ui128_468 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_468)
; CHECK: fffffffffffffffffffffffffffffffd 0
  %si128_468 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_468)
; CHECK: fffffffffffffffffffffffffffffffc 1
  %ui128_469 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_469)
; CHECK: fffffffffffffffffffffffffffffffc 0
  %si128_469 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %si128_469)
; CHECK: 7ffffffffffffffffffffffffffffffe 1
  %ui128_470 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_470)
; CHECK: 7ffffffffffffffffffffffffffffffe 1
  %si128_470 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_470)
; CHECK: 3ffffffffffffffffffffffffffffffe 1
  %ui128_471 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_471)
; CHECK: 3ffffffffffffffffffffffffffffffe 0
  %si128_471 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_471)
; CHECK: 7ffffffffffffffffffffffffffffffd 1
  %ui128_472 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_472)
; CHECK: 7ffffffffffffffffffffffffffffffd 0
  %si128_472 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_472)
; CHECK: 7fffffffffffffeffffffffffffffffe 1
  %ui128_473 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %ui128_473)
; CHECK: 7fffffffffffffeffffffffffffffffe 0
  %si128_473 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %si128_473)
; CHECK: 7fffffffffffffefffffffffffffffff 1
  %ui128_474 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %ui128_474)
; CHECK: 7fffffffffffffefffffffffffffffff 0
  %si128_474 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %si128_474)
; CHECK: 3ffffffffffffffffffffffffffffffd 1
  %ui128_475 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_475)
; CHECK: 3ffffffffffffffffffffffffffffffd 0
  %si128_475 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0xfffffffffffffffffffffffffffffffe, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_475)
; CHECK: 80000000000000000000000000000000 0
  %ui128_476 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_476)
; CHECK: 80000000000000000000000000000000 0
  %si128_476 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_476)
; CHECK: 80000000000000000000000000000001 0
  %ui128_477 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %ui128_477)
; CHECK: 80000000000000000000000000000001 0
  %si128_477 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %si128_477)
; CHECK: 80000000000000000000000000000002 0
  %ui128_478 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %ui128_478)
; CHECK: 80000000000000000000000000000002 0
  %si128_478 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %si128_478)
; CHECK: 80000000000000007fffffffffffffff 0
  %ui128_479 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_479)
; CHECK: 80000000000000007fffffffffffffff 0
  %si128_479 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %si128_479)
; CHECK: 80000000000000008000000000000000 0
  %ui128_480 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %ui128_480)
; CHECK: 80000000000000008000000000000000 0
  %si128_480 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %si128_480)
; CHECK: 8000000000000000fffffffffffffffe 0
  %ui128_481 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_481)
; CHECK: 8000000000000000fffffffffffffffe 0
  %si128_481 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_481)
; CHECK: 8000000000000000ffffffffffffffff 0
  %ui128_482 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_482)
; CHECK: 8000000000000000ffffffffffffffff 0
  %si128_482 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_482)
; CHECK: 80000000000000010000000000000000 0
  %ui128_483 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %ui128_483)
; CHECK: 80000000000000010000000000000000 0
  %si128_483 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %si128_483)
; CHECK: 80000000000000010000000000000001 0
  %ui128_484 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %ui128_484)
; CHECK: 80000000000000010000000000000001 0
  %si128_484 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %si128_484)
; CHECK: 80000000000000010000000000000002 0
  %ui128_485 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %ui128_485)
; CHECK: 80000000000000010000000000000002 0
  %si128_485 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %si128_485)
; CHECK: 80000000000000017fffffffffffffff 0
  %ui128_486 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_486)
; CHECK: 80000000000000017fffffffffffffff 0
  %si128_486 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %si128_486)
; CHECK: 80000000000000018000000000000000 0
  %ui128_487 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %ui128_487)
; CHECK: 80000000000000018000000000000000 0
  %si128_487 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %si128_487)
; CHECK: 8000000000000001fffffffffffffffe 0
  %ui128_488 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_488)
; CHECK: 8000000000000001fffffffffffffffe 0
  %si128_488 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_488)
; CHECK: 8000000000000001ffffffffffffffff 0
  %ui128_489 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_489)
; CHECK: 8000000000000001ffffffffffffffff 0
  %si128_489 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_489)
; CHECK: 7fffffffffffffff0000000000000000 1
  %ui128_490 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %ui128_490)
; CHECK: 7fffffffffffffff0000000000000000 1
  %si128_490 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %si128_490)
; CHECK: 7fffffffffffffff0000000000000001 1
  %ui128_491 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %ui128_491)
; CHECK: 7fffffffffffffff0000000000000001 1
  %si128_491 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %si128_491)
; CHECK: 7fffffffffffffff0000000000000002 1
  %ui128_492 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %ui128_492)
; CHECK: 7fffffffffffffff0000000000000002 1
  %si128_492 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %si128_492)
; CHECK: 7fffffffffffffffffffffffffffffff 1
  %ui128_493 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_493)
; CHECK: 7fffffffffffffffffffffffffffffff 1
  %si128_493 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_493)
; CHECK: 7ffffffffffffffffffffffffffffffe 1
  %ui128_494 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_494)
; CHECK: 7ffffffffffffffffffffffffffffffe 1
  %si128_494 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %si128_494)
; CHECK: 00000000000000000000000000000000 1
  %ui128_495 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_495)
; CHECK: 00000000000000000000000000000000 1
  %si128_495 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_495)
; CHECK: c0000000000000000000000000000000 0
  %ui128_496 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_496)
; CHECK: c0000000000000000000000000000000 0
  %si128_496 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_496)
; CHECK: ffffffffffffffffffffffffffffffff 0
  %ui128_497 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_497)
; CHECK: ffffffffffffffffffffffffffffffff 0
  %si128_497 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_497)
; CHECK: fffffffffffffff00000000000000000 0
  %ui128_498 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %ui128_498)
; CHECK: fffffffffffffff00000000000000000 0
  %si128_498 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %si128_498)
; CHECK: fffffffffffffff00000000000000001 0
  %ui128_499 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %ui128_499)
; CHECK: fffffffffffffff00000000000000001 0
  %si128_499 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %si128_499)
; CHECK: bfffffffffffffffffffffffffffffff 0
  %ui128_500 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_500)
; CHECK: bfffffffffffffffffffffffffffffff 0
  %si128_500 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x80000000000000000000000000000000, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_500)
; CHECK: 40000000000000000000000000000000 0
  %ui128_501 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_501)
; CHECK: 40000000000000000000000000000000 0
  %si128_501 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_501)
; CHECK: 40000000000000000000000000000001 0
  %ui128_502 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %ui128_502)
; CHECK: 40000000000000000000000000000001 0
  %si128_502 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %si128_502)
; CHECK: 40000000000000000000000000000002 0
  %ui128_503 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %ui128_503)
; CHECK: 40000000000000000000000000000002 0
  %si128_503 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %si128_503)
; CHECK: 40000000000000007fffffffffffffff 0
  %ui128_504 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_504)
; CHECK: 40000000000000007fffffffffffffff 0
  %si128_504 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %si128_504)
; CHECK: 40000000000000008000000000000000 0
  %ui128_505 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %ui128_505)
; CHECK: 40000000000000008000000000000000 0
  %si128_505 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %si128_505)
; CHECK: 4000000000000000fffffffffffffffe 0
  %ui128_506 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_506)
; CHECK: 4000000000000000fffffffffffffffe 0
  %si128_506 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_506)
; CHECK: 4000000000000000ffffffffffffffff 0
  %ui128_507 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_507)
; CHECK: 4000000000000000ffffffffffffffff 0
  %si128_507 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_507)
; CHECK: 40000000000000010000000000000000 0
  %ui128_508 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %ui128_508)
; CHECK: 40000000000000010000000000000000 0
  %si128_508 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %si128_508)
; CHECK: 40000000000000010000000000000001 0
  %ui128_509 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %ui128_509)
; CHECK: 40000000000000010000000000000001 0
  %si128_509 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %si128_509)
; CHECK: 40000000000000010000000000000002 0
  %ui128_510 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %ui128_510)
; CHECK: 40000000000000010000000000000002 0
  %si128_510 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %si128_510)
; CHECK: 40000000000000017fffffffffffffff 0
  %ui128_511 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_511)
; CHECK: 40000000000000017fffffffffffffff 0
  %si128_511 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %si128_511)
; CHECK: 40000000000000018000000000000000 0
  %ui128_512 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %ui128_512)
; CHECK: 40000000000000018000000000000000 0
  %si128_512 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %si128_512)
; CHECK: 4000000000000001fffffffffffffffe 0
  %ui128_513 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_513)
; CHECK: 4000000000000001fffffffffffffffe 0
  %si128_513 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_513)
; CHECK: 4000000000000001ffffffffffffffff 0
  %ui128_514 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_514)
; CHECK: 4000000000000001ffffffffffffffff 0
  %si128_514 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_514)
; CHECK: 3fffffffffffffff0000000000000000 1
  %ui128_515 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %ui128_515)
; CHECK: 3fffffffffffffff0000000000000000 0
  %si128_515 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %si128_515)
; CHECK: 3fffffffffffffff0000000000000001 1
  %ui128_516 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %ui128_516)
; CHECK: 3fffffffffffffff0000000000000001 0
  %si128_516 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %si128_516)
; CHECK: 3fffffffffffffff0000000000000002 1
  %ui128_517 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %ui128_517)
; CHECK: 3fffffffffffffff0000000000000002 0
  %si128_517 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %si128_517)
; CHECK: 3fffffffffffffffffffffffffffffff 1
  %ui128_518 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_518)
; CHECK: 3fffffffffffffffffffffffffffffff 0
  %si128_518 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_518)
; CHECK: 3ffffffffffffffffffffffffffffffe 1
  %ui128_519 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_519)
; CHECK: 3ffffffffffffffffffffffffffffffe 0
  %si128_519 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %si128_519)
; CHECK: c0000000000000000000000000000000 0
  %ui128_520 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_520)
; CHECK: c0000000000000000000000000000000 0
  %si128_520 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_520)
; CHECK: 80000000000000000000000000000000 0
  %ui128_521 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_521)
; CHECK: 80000000000000000000000000000000 1
  %si128_521 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_521)
; CHECK: bfffffffffffffffffffffffffffffff 0
  %ui128_522 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_522)
; CHECK: bfffffffffffffffffffffffffffffff 1
  %si128_522 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_522)
; CHECK: bffffffffffffff00000000000000000 0
  %ui128_523 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %ui128_523)
; CHECK: bffffffffffffff00000000000000000 1
  %si128_523 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %si128_523)
; CHECK: bffffffffffffff00000000000000001 0
  %ui128_524 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %ui128_524)
; CHECK: bffffffffffffff00000000000000001 1
  %si128_524 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %si128_524)
; CHECK: 7fffffffffffffffffffffffffffffff 0
  %ui128_525 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_525)
; CHECK: 7fffffffffffffffffffffffffffffff 0
  %si128_525 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x40000000000000000000000000000000, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_525)
; CHECK: 7fffffffffffffffffffffffffffffff 0
  %ui128_526 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_526)
; CHECK: 7fffffffffffffffffffffffffffffff 0
  %si128_526 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_526)
; CHECK: 80000000000000000000000000000000 0
  %ui128_527 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %ui128_527)
; CHECK: 80000000000000000000000000000000 1
  %si128_527 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %si128_527)
; CHECK: 80000000000000000000000000000001 0
  %ui128_528 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %ui128_528)
; CHECK: 80000000000000000000000000000001 1
  %si128_528 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %si128_528)
; CHECK: 80000000000000007ffffffffffffffe 0
  %ui128_529 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_529)
; CHECK: 80000000000000007ffffffffffffffe 1
  %si128_529 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %si128_529)
; CHECK: 80000000000000007fffffffffffffff 0
  %ui128_530 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %ui128_530)
; CHECK: 80000000000000007fffffffffffffff 1
  %si128_530 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %si128_530)
; CHECK: 8000000000000000fffffffffffffffd 0
  %ui128_531 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_531)
; CHECK: 8000000000000000fffffffffffffffd 1
  %si128_531 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_531)
; CHECK: 8000000000000000fffffffffffffffe 0
  %ui128_532 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_532)
; CHECK: 8000000000000000fffffffffffffffe 1
  %si128_532 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_532)
; CHECK: 8000000000000000ffffffffffffffff 0
  %ui128_533 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %ui128_533)
; CHECK: 8000000000000000ffffffffffffffff 1
  %si128_533 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %si128_533)
; CHECK: 80000000000000010000000000000000 0
  %ui128_534 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %ui128_534)
; CHECK: 80000000000000010000000000000000 1
  %si128_534 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %si128_534)
; CHECK: 80000000000000010000000000000001 0
  %ui128_535 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %ui128_535)
; CHECK: 80000000000000010000000000000001 1
  %si128_535 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %si128_535)
; CHECK: 80000000000000017ffffffffffffffe 0
  %ui128_536 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_536)
; CHECK: 80000000000000017ffffffffffffffe 1
  %si128_536 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %si128_536)
; CHECK: 80000000000000017fffffffffffffff 0
  %ui128_537 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %ui128_537)
; CHECK: 80000000000000017fffffffffffffff 1
  %si128_537 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %si128_537)
; CHECK: 8000000000000001fffffffffffffffd 0
  %ui128_538 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_538)
; CHECK: 8000000000000001fffffffffffffffd 1
  %si128_538 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_538)
; CHECK: 8000000000000001fffffffffffffffe 0
  %ui128_539 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_539)
; CHECK: 8000000000000001fffffffffffffffe 1
  %si128_539 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_539)
; CHECK: 7ffffffffffffffeffffffffffffffff 1
  %ui128_540 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %ui128_540)
; CHECK: 7ffffffffffffffeffffffffffffffff 0
  %si128_540 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %si128_540)
; CHECK: 7fffffffffffffff0000000000000000 1
  %ui128_541 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %ui128_541)
; CHECK: 7fffffffffffffff0000000000000000 0
  %si128_541 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %si128_541)
; CHECK: 7fffffffffffffff0000000000000001 1
  %ui128_542 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %ui128_542)
; CHECK: 7fffffffffffffff0000000000000001 0
  %si128_542 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %si128_542)
; CHECK: 7ffffffffffffffffffffffffffffffe 1
  %ui128_543 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_543)
; CHECK: 7ffffffffffffffffffffffffffffffe 0
  %si128_543 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_543)
; CHECK: 7ffffffffffffffffffffffffffffffd 1
  %ui128_544 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_544)
; CHECK: 7ffffffffffffffffffffffffffffffd 0
  %si128_544 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %si128_544)
; CHECK: ffffffffffffffffffffffffffffffff 0
  %ui128_545 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_545)
; CHECK: ffffffffffffffffffffffffffffffff 0
  %si128_545 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_545)
; CHECK: bfffffffffffffffffffffffffffffff 0
  %ui128_546 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_546)
; CHECK: bfffffffffffffffffffffffffffffff 1
  %si128_546 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_546)
; CHECK: fffffffffffffffffffffffffffffffe 0
  %ui128_547 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_547)
; CHECK: fffffffffffffffffffffffffffffffe 1
  %si128_547 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_547)
; CHECK: ffffffffffffffefffffffffffffffff 0
  %ui128_548 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %ui128_548)
; CHECK: ffffffffffffffefffffffffffffffff 1
  %si128_548 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %si128_548)
; CHECK: fffffffffffffff00000000000000000 0
  %ui128_549 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %ui128_549)
; CHECK: fffffffffffffff00000000000000000 1
  %si128_549 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %si128_549)
; CHECK: bffffffffffffffffffffffffffffffe 0
  %ui128_550 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_550)
; CHECK: bffffffffffffffffffffffffffffffe 1
  %si128_550 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7fffffffffffffffffffffffffffffff, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_550)
; CHECK: 7ffffffffffffff00000000000000000 0
  %ui128_551 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_551)
; CHECK: 7ffffffffffffff00000000000000000 0
  %si128_551 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_551)
; CHECK: 7ffffffffffffff00000000000000001 0
  %ui128_552 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %ui128_552)
; CHECK: 7ffffffffffffff00000000000000001 0
  %si128_552 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %si128_552)
; CHECK: 7ffffffffffffff00000000000000002 0
  %ui128_553 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %ui128_553)
; CHECK: 7ffffffffffffff00000000000000002 0
  %si128_553 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %si128_553)
; CHECK: 7ffffffffffffff07fffffffffffffff 0
  %ui128_554 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_554)
; CHECK: 7ffffffffffffff07fffffffffffffff 0
  %si128_554 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %si128_554)
; CHECK: 7ffffffffffffff08000000000000000 0
  %ui128_555 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %ui128_555)
; CHECK: 7ffffffffffffff08000000000000000 0
  %si128_555 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %si128_555)
; CHECK: 7ffffffffffffff0fffffffffffffffe 0
  %ui128_556 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_556)
; CHECK: 7ffffffffffffff0fffffffffffffffe 0
  %si128_556 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_556)
; CHECK: 7ffffffffffffff0ffffffffffffffff 0
  %ui128_557 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_557)
; CHECK: 7ffffffffffffff0ffffffffffffffff 0
  %si128_557 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_557)
; CHECK: 7ffffffffffffff10000000000000000 0
  %ui128_558 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %ui128_558)
; CHECK: 7ffffffffffffff10000000000000000 0
  %si128_558 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %si128_558)
; CHECK: 7ffffffffffffff10000000000000001 0
  %ui128_559 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %ui128_559)
; CHECK: 7ffffffffffffff10000000000000001 0
  %si128_559 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %si128_559)
; CHECK: 7ffffffffffffff10000000000000002 0
  %ui128_560 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %ui128_560)
; CHECK: 7ffffffffffffff10000000000000002 0
  %si128_560 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %si128_560)
; CHECK: 7ffffffffffffff17fffffffffffffff 0
  %ui128_561 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_561)
; CHECK: 7ffffffffffffff17fffffffffffffff 0
  %si128_561 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %si128_561)
; CHECK: 7ffffffffffffff18000000000000000 0
  %ui128_562 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %ui128_562)
; CHECK: 7ffffffffffffff18000000000000000 0
  %si128_562 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %si128_562)
; CHECK: 7ffffffffffffff1fffffffffffffffe 0
  %ui128_563 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_563)
; CHECK: 7ffffffffffffff1fffffffffffffffe 0
  %si128_563 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_563)
; CHECK: 7ffffffffffffff1ffffffffffffffff 0
  %ui128_564 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_564)
; CHECK: 7ffffffffffffff1ffffffffffffffff 0
  %si128_564 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_564)
; CHECK: 7fffffffffffffef0000000000000000 1
  %ui128_565 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %ui128_565)
; CHECK: 7fffffffffffffef0000000000000000 0
  %si128_565 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %si128_565)
; CHECK: 7fffffffffffffef0000000000000001 1
  %ui128_566 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %ui128_566)
; CHECK: 7fffffffffffffef0000000000000001 0
  %si128_566 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %si128_566)
; CHECK: 7fffffffffffffef0000000000000002 1
  %ui128_567 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %ui128_567)
; CHECK: 7fffffffffffffef0000000000000002 0
  %si128_567 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %si128_567)
; CHECK: 7fffffffffffffefffffffffffffffff 1
  %ui128_568 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_568)
; CHECK: 7fffffffffffffefffffffffffffffff 0
  %si128_568 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_568)
; CHECK: 7fffffffffffffeffffffffffffffffe 1
  %ui128_569 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_569)
; CHECK: 7fffffffffffffeffffffffffffffffe 0
  %si128_569 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %si128_569)
; CHECK: fffffffffffffff00000000000000000 0
  %ui128_570 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_570)
; CHECK: fffffffffffffff00000000000000000 0
  %si128_570 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_570)
; CHECK: bffffffffffffff00000000000000000 0
  %ui128_571 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_571)
; CHECK: bffffffffffffff00000000000000000 1
  %si128_571 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_571)
; CHECK: ffffffffffffffefffffffffffffffff 0
  %ui128_572 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_572)
; CHECK: ffffffffffffffefffffffffffffffff 1
  %si128_572 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_572)
; CHECK: ffffffffffffffe00000000000000000 0
  %ui128_573 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %ui128_573)
; CHECK: ffffffffffffffe00000000000000000 1
  %si128_573 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %si128_573)
; CHECK: ffffffffffffffe00000000000000001 0
  %ui128_574 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %ui128_574)
; CHECK: ffffffffffffffe00000000000000001 1
  %si128_574 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %si128_574)
; CHECK: bfffffffffffffefffffffffffffffff 0
  %ui128_575 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_575)
; CHECK: bfffffffffffffefffffffffffffffff 1
  %si128_575 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000000, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_575)
; CHECK: 7ffffffffffffff00000000000000001 0
  %ui128_576 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_576)
; CHECK: 7ffffffffffffff00000000000000001 0
  %si128_576 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_576)
; CHECK: 7ffffffffffffff00000000000000002 0
  %ui128_577 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %ui128_577)
; CHECK: 7ffffffffffffff00000000000000002 0
  %si128_577 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %si128_577)
; CHECK: 7ffffffffffffff00000000000000003 0
  %ui128_578 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %ui128_578)
; CHECK: 7ffffffffffffff00000000000000003 0
  %si128_578 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %si128_578)
; CHECK: 7ffffffffffffff08000000000000000 0
  %ui128_579 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_579)
; CHECK: 7ffffffffffffff08000000000000000 0
  %si128_579 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %si128_579)
; CHECK: 7ffffffffffffff08000000000000001 0
  %ui128_580 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %ui128_580)
; CHECK: 7ffffffffffffff08000000000000001 0
  %si128_580 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %si128_580)
; CHECK: 7ffffffffffffff0ffffffffffffffff 0
  %ui128_581 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_581)
; CHECK: 7ffffffffffffff0ffffffffffffffff 0
  %si128_581 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_581)
; CHECK: 7ffffffffffffff10000000000000000 0
  %ui128_582 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_582)
; CHECK: 7ffffffffffffff10000000000000000 0
  %si128_582 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_582)
; CHECK: 7ffffffffffffff10000000000000001 0
  %ui128_583 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %ui128_583)
; CHECK: 7ffffffffffffff10000000000000001 0
  %si128_583 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %si128_583)
; CHECK: 7ffffffffffffff10000000000000002 0
  %ui128_584 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %ui128_584)
; CHECK: 7ffffffffffffff10000000000000002 0
  %si128_584 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %si128_584)
; CHECK: 7ffffffffffffff10000000000000003 0
  %ui128_585 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %ui128_585)
; CHECK: 7ffffffffffffff10000000000000003 0
  %si128_585 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %si128_585)
; CHECK: 7ffffffffffffff18000000000000000 0
  %ui128_586 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_586)
; CHECK: 7ffffffffffffff18000000000000000 0
  %si128_586 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %si128_586)
; CHECK: 7ffffffffffffff18000000000000001 0
  %ui128_587 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %ui128_587)
; CHECK: 7ffffffffffffff18000000000000001 0
  %si128_587 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %si128_587)
; CHECK: 7ffffffffffffff1ffffffffffffffff 0
  %ui128_588 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_588)
; CHECK: 7ffffffffffffff1ffffffffffffffff 0
  %si128_588 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_588)
; CHECK: 7ffffffffffffff20000000000000000 0
  %ui128_589 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_589)
; CHECK: 7ffffffffffffff20000000000000000 0
  %si128_589 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_589)
; CHECK: 7fffffffffffffef0000000000000001 1
  %ui128_590 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %ui128_590)
; CHECK: 7fffffffffffffef0000000000000001 0
  %si128_590 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %si128_590)
; CHECK: 7fffffffffffffef0000000000000002 1
  %ui128_591 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %ui128_591)
; CHECK: 7fffffffffffffef0000000000000002 0
  %si128_591 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %si128_591)
; CHECK: 7fffffffffffffef0000000000000003 1
  %ui128_592 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %ui128_592)
; CHECK: 7fffffffffffffef0000000000000003 0
  %si128_592 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %si128_592)
; CHECK: 7ffffffffffffff00000000000000000 1
  %ui128_593 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_593)
; CHECK: 7ffffffffffffff00000000000000000 0
  %si128_593 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_593)
; CHECK: 7fffffffffffffefffffffffffffffff 1
  %ui128_594 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_594)
; CHECK: 7fffffffffffffefffffffffffffffff 0
  %si128_594 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %si128_594)
; CHECK: fffffffffffffff00000000000000001 0
  %ui128_595 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_595)
; CHECK: fffffffffffffff00000000000000001 0
  %si128_595 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_595)
; CHECK: bffffffffffffff00000000000000001 0
  %ui128_596 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_596)
; CHECK: bffffffffffffff00000000000000001 1
  %si128_596 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_596)
; CHECK: fffffffffffffff00000000000000000 0
  %ui128_597 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_597)
; CHECK: fffffffffffffff00000000000000000 1
  %si128_597 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_597)
; CHECK: ffffffffffffffe00000000000000001 0
  %ui128_598 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %ui128_598)
; CHECK: ffffffffffffffe00000000000000001 1
  %si128_598 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %si128_598)
; CHECK: ffffffffffffffe00000000000000002 0
  %ui128_599 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %ui128_599)
; CHECK: ffffffffffffffe00000000000000002 1
  %si128_599 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %si128_599)
; CHECK: bffffffffffffff00000000000000000 0
  %ui128_600 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_600)
; CHECK: bffffffffffffff00000000000000000 1
  %si128_600 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x7ffffffffffffff00000000000000001, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_600)
; CHECK: 3fffffffffffffffffffffffffffffff 0
  %ui128_601 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_601)
; CHECK: 3fffffffffffffffffffffffffffffff 0
  %si128_601 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x00000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_601)
; CHECK: 40000000000000000000000000000000 0
  %ui128_602 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %ui128_602)
; CHECK: 40000000000000000000000000000000 0
  %si128_602 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x00000000000000000000000000000001)
  call void @print_i128({i128, i1} %si128_602)
; CHECK: 40000000000000000000000000000001 0
  %ui128_603 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %ui128_603)
; CHECK: 40000000000000000000000000000001 0
  %si128_603 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x00000000000000000000000000000002)
  call void @print_i128({i128, i1} %si128_603)
; CHECK: 40000000000000007ffffffffffffffe 0
  %ui128_604 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_604)
; CHECK: 40000000000000007ffffffffffffffe 0
  %si128_604 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x00000000000000007fffffffffffffff)
  call void @print_i128({i128, i1} %si128_604)
; CHECK: 40000000000000007fffffffffffffff 0
  %ui128_605 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %ui128_605)
; CHECK: 40000000000000007fffffffffffffff 0
  %si128_605 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x00000000000000008000000000000000)
  call void @print_i128({i128, i1} %si128_605)
; CHECK: 4000000000000000fffffffffffffffd 0
  %ui128_606 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_606)
; CHECK: 4000000000000000fffffffffffffffd 0
  %si128_606 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x0000000000000000fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_606)
; CHECK: 4000000000000000fffffffffffffffe 0
  %ui128_607 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_607)
; CHECK: 4000000000000000fffffffffffffffe 0
  %si128_607 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x0000000000000000ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_607)
; CHECK: 4000000000000000ffffffffffffffff 0
  %ui128_608 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %ui128_608)
; CHECK: 4000000000000000ffffffffffffffff 0
  %si128_608 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x00000000000000010000000000000000)
  call void @print_i128({i128, i1} %si128_608)
; CHECK: 40000000000000010000000000000000 0
  %ui128_609 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %ui128_609)
; CHECK: 40000000000000010000000000000000 0
  %si128_609 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x00000000000000010000000000000001)
  call void @print_i128({i128, i1} %si128_609)
; CHECK: 40000000000000010000000000000001 0
  %ui128_610 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %ui128_610)
; CHECK: 40000000000000010000000000000001 0
  %si128_610 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x00000000000000010000000000000002)
  call void @print_i128({i128, i1} %si128_610)
; CHECK: 40000000000000017ffffffffffffffe 0
  %ui128_611 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %ui128_611)
; CHECK: 40000000000000017ffffffffffffffe 0
  %si128_611 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x00000000000000017fffffffffffffff)
  call void @print_i128({i128, i1} %si128_611)
; CHECK: 40000000000000017fffffffffffffff 0
  %ui128_612 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %ui128_612)
; CHECK: 40000000000000017fffffffffffffff 0
  %si128_612 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x00000000000000018000000000000000)
  call void @print_i128({i128, i1} %si128_612)
; CHECK: 4000000000000001fffffffffffffffd 0
  %ui128_613 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_613)
; CHECK: 4000000000000001fffffffffffffffd 0
  %si128_613 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x0000000000000001fffffffffffffffe)
  call void @print_i128({i128, i1} %si128_613)
; CHECK: 4000000000000001fffffffffffffffe 0
  %ui128_614 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_614)
; CHECK: 4000000000000001fffffffffffffffe 0
  %si128_614 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x0000000000000001ffffffffffffffff)
  call void @print_i128({i128, i1} %si128_614)
; CHECK: 3ffffffffffffffeffffffffffffffff 1
  %ui128_615 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %ui128_615)
; CHECK: 3ffffffffffffffeffffffffffffffff 0
  %si128_615 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0xffffffffffffffff0000000000000000)
  call void @print_i128({i128, i1} %si128_615)
; CHECK: 3fffffffffffffff0000000000000000 1
  %ui128_616 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %ui128_616)
; CHECK: 3fffffffffffffff0000000000000000 0
  %si128_616 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0xffffffffffffffff0000000000000001)
  call void @print_i128({i128, i1} %si128_616)
; CHECK: 3fffffffffffffff0000000000000001 1
  %ui128_617 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %ui128_617)
; CHECK: 3fffffffffffffff0000000000000001 0
  %si128_617 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0xffffffffffffffff0000000000000002)
  call void @print_i128({i128, i1} %si128_617)
; CHECK: 3ffffffffffffffffffffffffffffffe 1
  %ui128_618 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_618)
; CHECK: 3ffffffffffffffffffffffffffffffe 0
  %si128_618 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0xffffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_618)
; CHECK: 3ffffffffffffffffffffffffffffffd 1
  %ui128_619 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %ui128_619)
; CHECK: 3ffffffffffffffffffffffffffffffd 0
  %si128_619 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0xfffffffffffffffffffffffffffffffe)
  call void @print_i128({i128, i1} %si128_619)
; CHECK: bfffffffffffffffffffffffffffffff 0
  %ui128_620 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_620)
; CHECK: bfffffffffffffffffffffffffffffff 0
  %si128_620 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x80000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_620)
; CHECK: 7fffffffffffffffffffffffffffffff 0
  %ui128_621 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %ui128_621)
; CHECK: 7fffffffffffffffffffffffffffffff 0
  %si128_621 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x40000000000000000000000000000000)
  call void @print_i128({i128, i1} %si128_621)
; CHECK: bffffffffffffffffffffffffffffffe 0
  %ui128_622 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_622)
; CHECK: bffffffffffffffffffffffffffffffe 1
  %si128_622 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x7fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_622)
; CHECK: bfffffffffffffefffffffffffffffff 0
  %ui128_623 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %ui128_623)
; CHECK: bfffffffffffffefffffffffffffffff 1
  %si128_623 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x7ffffffffffffff00000000000000000)
  call void @print_i128({i128, i1} %si128_623)
; CHECK: bffffffffffffff00000000000000000 0
  %ui128_624 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %ui128_624)
; CHECK: bffffffffffffff00000000000000000 1
  %si128_624 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x7ffffffffffffff00000000000000001)
  call void @print_i128({i128, i1} %si128_624)
; CHECK: 7ffffffffffffffffffffffffffffffe 0
  %ui128_625 = call {i128, i1} @llvm.uadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %ui128_625)
; CHECK: 7ffffffffffffffffffffffffffffffe 0
  %si128_625 = call {i128, i1} @llvm.sadd.with.overflow(i128 u0x3fffffffffffffffffffffffffffffff, i128 u0x3fffffffffffffffffffffffffffffff)
  call void @print_i128({i128, i1} %si128_625)

  ret i32 0
}
