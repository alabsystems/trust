; NOTE: Do not autogenerate
; SPDX-FileCopyrightText: 2025 Contributors to TPDE <https://tpde.org>
; SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

; RUN: tpde-llc --target=x86_64 < %s | llvm-readelf -Sg - | FileCheck %s
; RUN: tpde-llc --target=aarch64 < %s | llvm-readelf -Sg - | FileCheck %s

; CHECK: Section Headers:
; CHECK: [{{ *}}[[C1_GROUP:[0-9]+]]]   .group      GROUP      {{[0-9a-f]+}} {{[0-9a-f]+}} {{[0-9a-f]+}} {{0*4}} {{[0-9]+}} {{[0-9]+}} 4
; CHECK: [{{ *}}[[INIT_ARRAY_IDX:[0-9]+]]] .init_array INIT_ARRAY {{[0-9a-f]+}} {{[0-9a-f]+}} {{0*8}} {{0+}} WAG 0 0 8
; CHECK-NEXT: .rela.init_array RELA {{[0-9a-f]+}} {{[0-9a-f]+}} {{0*18}} {{0*18}} IG {{[0-9]+}} [[INIT_ARRAY_IDX]] 8

; CHECK: COMDAT group section [{{ *}}[[C1_GROUP]]] `.group' [c1] contains [[#]] sections:
; CHECK: [{{ *}}[[INIT_ARRAY_IDX]]]

$c1 = comdat any
@c1 = global i32 1, align 4, comdat

@llvm.global_ctors = appending global [1 x { i32, ptr, ptr }] [{ i32, ptr, ptr } { i32 65535, ptr @f, ptr @c1 }]

declare void @f()
