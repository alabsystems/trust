; NOTE: Do not autogenerate
; SPDX-FileCopyrightText: 2025 Contributors to TPDE <https://tpde.org>
; SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

; RUN: tpde-llc --target=x86_64 %s | llvm-readelf -SrW - | FileCheck %s -check-prefixes=X64,CHECK
; RUN: tpde-llc --target=aarch64 %s | llvm-readelf -SrW - | FileCheck %s -check-prefixes=ARM64,CHECK

; COM: Check symbol table
; CHECK: [{{ *}}[[DATA_IDX:[0-9]+]]] .data PROGBITS {{[0-9a-f]+}} {{[0-9a-f]+}} {{0*8}} {{0+}} WA 0 0 8
; CHECK-NEXT: .rela.data RELA {{[0-9a-f]+}} {{[0-9a-f]+}} {{0*18}} {{0*18}} I {{[0-9]+}} [[DATA_IDX]] 8
; CHECK: [{{ *}}[[DATA_RELRO_IDX:[0-9]+]]] .data.rel.ro PROGBITS {{[0-9a-f]+}} {{[0-9a-f]+}} {{0*8}} {{0+}} WA 0 0 8
; CHECK-NEXT: .rela.data.rel.ro RELA {{[0-9a-f]+}} {{[0-9a-f]+}} {{0*18}} {{0*18}} I {{[0-9]+}} [[DATA_RELRO_IDX]] 8

; COM: Check relocations
; X64: Relocation section '.rela.data'
; X64-NEXT: Offset           Info          Type        Symbol's Value
; X64-NEXT: 0000000000000000 {{[0-9a-f]+}} R_X86_64_64 0000000000000000 x + 0
; X64-EMPTY:
; ARM64: Relocation section '.rela.data'
; ARM64-NEXT: Offset           Info          Type            Symbol's Value
; ARM64-NEXT: 0000000000000000 {{[0-9a-f]+}} R_AARCH64_ABS64 0000000000000000 x + 0
; ARM64-EMPTY:

; X64: Relocation section '.rela.data.rel.ro'
; X64-NEXT: Offset           Info          Type        Symbol's Value
; X64-NEXT: 0000000000000000 {{[0-9a-f]+}} R_X86_64_64 0000000000000000 y + 0
; X64-EMPTY:
; ARM64: Relocation section '.rela.data.rel.ro'
; ARM64-NEXT: Offset           Info          Type            Symbol's Value
; ARM64-NEXT: 0000000000000000 {{[0-9a-f]+}} R_AARCH64_ABS64 0000000000000000 y + 0
; ARM64-EMPTY:

@x = external global i32, align 4
@y = external global i32, align 4
@sym1 = global ptr @x, align 8
@sym2 = constant ptr @y, align 8
