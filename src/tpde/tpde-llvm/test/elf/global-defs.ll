; NOTE: Do not autogenerate
; SPDX-FileCopyrightText: 2025 Contributors to TPDE <https://tpde.org>
; SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

; RUN: tpde-llc --target=x86_64 < %s | llvm-readelf -Ss - | FileCheck %s
; RUN: tpde-llc --target=aarch64 < %s | llvm-readelf -Ss - | FileCheck %s

; CHECK: Section Headers:
; CHECK-DAG: [{{ *}}[[RODATA_IDX:[0-9]+]]] .rodata PROGBITS {{[0-9a-f]+}} {{[0-9a-f]+}} {{[0-9a-f]+}} {{0+}} A 0 0 {{[0-9]+}}
; CHECK-DAG: [{{ *}}[[DATA_IDX:[0-9]+]]] .data PROGBITS {{[0-9a-f]+}} {{[0-9a-f]+}} {{[0-9a-f]+}} {{0+}} WA 0 0 {{[0-9]+}}
; CHECK-DAG: [{{ *}}[[DATA_RELRO_IDX:[0-9]+]]] .data.rel.ro PROGBITS {{[0-9a-f]+}} {{[0-9a-f]+}} {{[0-9a-f]+}} {{0+}} WA 0 0 {{[0-9]+}}
; CHECK-DAG: [{{ *}}[[BSS_IDX:[0-9]+]]] .bss NOBITS {{[0-9a-f]+}} {{[0-9a-f]+}} {{[0-9a-f]+}} {{0+}} WA 0 0 {{[0-9]+}}
; CHECK-DAG: [{{ *}}[[TDATA_IDX:[0-9]+]]] .tdata PROGBITS {{[0-9a-f]+}} {{[0-9a-f]+}} {{[0-9a-f]+}} {{0+}} WAT 0 0 {{[0-9]+}}
; CHECK-DAG: [{{ *}}[[TBSS_IDX:[0-9]+]]] .tbss NOBITS {{[0-9a-f]+}} {{[0-9a-f]+}} {{[0-9a-f]+}} {{0+}} WAT 0 0 {{[0-9]+}}

; CHECK: Symbol table '.symtab'
; CHECK-DAG:  4 OBJECT  GLOBAL DEFAULT [[BSS_IDX]]          int_zero
; CHECK-DAG:  4 OBJECT  GLOBAL DEFAULT [[DATA_IDX]]         int_one
; CHECK-DAG:  4 OBJECT  GLOBAL DEFAULT [[RODATA_IDX]]       cint_zero
; CHECK-DAG:  4 OBJECT  GLOBAL DEFAULT [[RODATA_IDX]]       cint_one
; CHECK-DAG:  4 TLS     GLOBAL DEFAULT [[TBSS_IDX]]         tint_zero
; CHECK-DAG:  4 TLS     GLOBAL DEFAULT [[TDATA_IDX]]        tint_one
; CHECK-DAG:  8 OBJECT  GLOBAL DEFAULT [[BSS_IDX]]          ptr_zero
; CHECK-DAG:  8 OBJECT  GLOBAL DEFAULT [[DATA_IDX]]         ptr_one
; CHECK-DAG:  8 OBJECT  GLOBAL DEFAULT [[RODATA_IDX]]       cptr_zero
; CHECK-DAG:  8 OBJECT  GLOBAL DEFAULT [[DATA_RELRO_IDX]]   cptr_one
; CHECK-DAG:  8 TLS     GLOBAL DEFAULT [[TBSS_IDX]]         tptr_zero
; CHECK-DAG:  8 TLS     GLOBAL DEFAULT [[TDATA_IDX]]        tptr_one
; CHECK-DAG: 20 OBJECT  GLOBAL DEFAULT [[BSS_IDX]]          struct_zero
; CHECK-DAG: 20 OBJECT  GLOBAL DEFAULT [[DATA_IDX]]         struct_one
; CHECK-DAG: 20 OBJECT  GLOBAL DEFAULT [[RODATA_IDX]]       cstruct_zero
; CHECK-DAG: 20 OBJECT  GLOBAL DEFAULT [[RODATA_IDX]]       cstruct_one
; CHECK-DAG: 20 TLS     GLOBAL DEFAULT [[TBSS_IDX]]         tstruct_zero
; CHECK-DAG: 20 TLS     GLOBAL DEFAULT [[TDATA_IDX]]        tstruct_one

@int_zero = global i32 0, align 4
@int_one = global i32 1, align 4
@cint_zero = constant i32 0, align 4
@cint_one = constant i32 1, align 4
@tint_zero = thread_local global i32 0, align 4
@tint_one = thread_local global i32 1, align 4

@ptr_zero = global ptr null, align 8
@ptr_one = global ptr @cint_one, align 8
@cptr_zero = constant ptr null, align 8
@cptr_one = constant ptr @cint_one, align 8
@tptr_zero = thread_local global ptr null, align 8
@tptr_one = thread_local global ptr @cint_one, align 8

@struct_zero = global {i32, [4 x i32]} zeroinitializer, align 4
@struct_one = global {i32, [4 x i32]} {i32 1, [4 x i32] zeroinitializer}, align 4
@cstruct_zero = constant {i32, [4 x i32]} zeroinitializer, align 4
@cstruct_one = constant {i32, [4 x i32]} {i32 1, [4 x i32] zeroinitializer}, align 4
@tstruct_zero = thread_local global {i32, [4 x i32]} zeroinitializer, align 4
@tstruct_one = thread_local global {i32, [4 x i32]} {i32 1, [4 x i32] zeroinitializer}, align 4
