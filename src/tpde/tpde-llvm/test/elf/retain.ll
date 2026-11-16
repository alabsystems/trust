; NOTE: Do not autogenerate
; SPDX-FileCopyrightText: 2025 Contributors to TPDE <https://tpde.org>
; SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

; RUN: tpde-llc --target=x86_64 < %s | llvm-readelf -Ss - | FileCheck %s
; RUN: tpde-llc --target=aarch64 < %s | llvm-readelf -Ss - | FileCheck %s

; CHECK: Section Headers:
; CHECK-DAG: [{{ *}}[[SEC1:[0-9]+]]] sec1 PROGBITS {{[0-9a-f]+}} {{[0-9a-f]+}} {{[0-9a-f]+}} {{0+}} AXR 0 0 {{[0-9]+}}
; CHECK-DAG: [{{ *}}[[TEXT_RETAIN:[0-9]+]]] .text PROGBITS {{[0-9a-f]+}} {{[0-9a-f]+}} {{[0-9a-f]+}} {{0+}} AXR 0 0 {{[0-9]+}}
; CHECK-DAG: [{{ *}}[[TEXT:[0-9]+]]] .text PROGBITS {{[0-9a-f]+}} {{[0-9a-f]+}} {{[0-9a-f]+}} {{0+}} AX 0 0 {{[0-9]+}}

; CHECK: Symbol table '.symtab'
; CHECK-DAG: {{[0-9]+}} FUNC    GLOBAL DEFAULT [[SEC1]]        fsec1
; CHECK-DAG: {{[0-9]+}} FUNC    GLOBAL DEFAULT [[TEXT_RETAIN]] ftext
; CHECK-DAG: {{[0-9]+}} FUNC    GLOBAL DEFAULT [[TEXT]]        text

@llvm.used = appending global [2 x ptr] [ptr @fsec1, ptr @ftext]

define void @fsec1() section "sec1" {
  ret void
}

define void @ftext() {
  ret void
}

define void @text() {
  ret void
}
