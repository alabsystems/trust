; NOTE: Do not autogenerate
; SPDX-FileCopyrightText: 2025 Contributors to TPDE <https://tpde.org>
; SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

; RUN: tpde-llc --target=x86_64 %s | llvm-readelf -SrW - | FileCheck %s -check-prefixes=X64,CHECK
; RUN: tpde-llc --target=aarch64 %s | llvm-readelf -SrW - | FileCheck %s -check-prefixes=ARM64,CHECK

; COM: Check symbol table
; CHECK: [{{ *}}[[INIT_ARRAY_IDX:[0-9]+]]] .init_array INIT_ARRAY {{[0-9a-f]+}} {{[0-9a-f]+}} {{0*8}} {{0+}} WA 0 0 8
; CHECK-NEXT: .rela.init_array RELA {{[0-9a-f]+}} {{[0-9a-f]+}} {{0*18}} {{0*18}} I {{[0-9]+}} [[INIT_ARRAY_IDX]] 8
; CHECK: [{{ *}}[[FINI_ARRAY_IDX:[0-9]+]]] .fini_array FINI_ARRAY {{[0-9a-f]+}} {{[0-9a-f]+}} {{0*10}} {{0+}} WA 0 0 8
; CHECK-NEXT: .rela.fini_array RELA {{[0-9a-f]+}} {{[0-9a-f]+}} {{0*30}} {{0*18}} I {{[0-9]+}} [[FINI_ARRAY_IDX]] 8

; COM: Check relocations
; X64: Relocation section '.rela.init_array'
; X64-NEXT: Offset           Info          Type        Symbol's Value
; X64-NEXT: 0000000000000000 {{[0-9a-f]+}} R_X86_64_64 0000000000000000 f + 0
; X64-EMPTY:
; ARM64: Relocation section '.rela.init_array'
; ARM64-NEXT: Offset           Info          Type            Symbol's Value
; ARM64-NEXT: 0000000000000000 {{[0-9a-f]+}} R_AARCH64_ABS64 0000000000000000 f + 0
; ARM64-EMPTY:

; X64: Relocation section '.rela.fini_array'
; X64-NEXT: Offset           Info          Type        Symbol's Value
; X64-NEXT: 0000000000000000 {{[0-9a-f]+}} R_X86_64_64 0000000000000000 g + 0
; X64-NEXT: 0000000000000008 {{[0-9a-f]+}} R_X86_64_64 0000000000000000 h + 0
; X64-EMPTY:
; ARM64: Relocation section '.rela.fini_array'
; ARM64-NEXT: Offset           Info          Type            Symbol's Value
; ARM64-NEXT: 0000000000000000 {{[0-9a-f]+}} R_AARCH64_ABS64 0000000000000000 g + 0
; ARM64-NEXT: 0000000000000008 {{[0-9a-f]+}} R_AARCH64_ABS64 0000000000000000 h + 0
; ARM64-EMPTY:

@llvm.global_ctors = appending global [1 x { i32, ptr, ptr }] [{ i32, ptr, ptr } { i32 65535, ptr @f, ptr null }]
@llvm.global_dtors = appending global [2 x { i32, ptr, ptr }] [{ i32, ptr, ptr } { i32 65535, ptr @g, ptr null }, { i32, ptr, ptr } { i32 65535, ptr @h, ptr null }]

declare void @f()
declare void @g()
declare void @h()
