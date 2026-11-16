; NOTE: Do not autogenerate
; SPDX-FileCopyrightText: 2025 Contributors to TPDE <https://tpde.org>
; SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

; RUN: tpde-llc --target=x86_64 < %s | llvm-readelf -s - | FileCheck %s
; RUN: tpde-llc --target=aarch64 < %s | llvm-readelf -s - | FileCheck %s

; TODO: make sure globals with private linkage don't end up in symbol table
; CHECK-DAG: NOTYPE  GLOBAL DEFAULT         UND dec_glob_default
; CHECK-DAG: NOTYPE  GLOBAL HIDDEN          UND dec_glob_hidden
; CHECK-DAG: NOTYPE  GLOBAL PROTECTED       UND dec_glob_protected
; CHECK-DAG: OBJECT  GLOBAL DEFAULT   {{[0-9]+}} def_glob_default
; CHECK-DAG: OBJECT  GLOBAL HIDDEN    {{[0-9]+}} def_glob_hidden
; CHECK-DAG: OBJECT  GLOBAL PROTECTED {{[0-9]+}} def_glob_protected
; CHECK-DAG: FUNC    GLOBAL DEFAULT   {{[0-9]+}} def_fn_default
; CHECK-DAG: FUNC    GLOBAL HIDDEN    {{[0-9]+}} def_fn_hidden
; CHECK-DAG: FUNC    WEAK   HIDDEN    {{[0-9]+}} def_fn_hidden_linkonce_odr
; CHECK-DAG: FUNC    GLOBAL PROTECTED {{[0-9]+}} def_fn_protected

@dec_glob_default = external global i32, align 4
@def_glob_default = global i32 100, align 4

@dec_glob_hidden = external hidden global i32, align 4
@def_glob_hidden = hidden global i32 100, align 4

@dec_glob_protected = external protected global i32, align 4
@def_glob_protected = protected global i32 100, align 4

define void @def_fn_default() {
  ret void
}

define hidden void @def_fn_hidden() {
  ret void
}

define linkonce_odr hidden void @def_fn_hidden_linkonce_odr() {
  ret void
}

define protected void @def_fn_protected() {
  ret void
}

; Ensure that all symbols end up in the symbol table.
define void @use() {
  store volatile ptr @dec_glob_default, ptr null
  store volatile ptr @def_glob_default, ptr null
  store volatile ptr @dec_glob_hidden, ptr null
  store volatile ptr @def_glob_hidden, ptr null
  store volatile ptr @dec_glob_protected, ptr null
  store volatile ptr @def_glob_protected, ptr null
  store volatile ptr @def_fn_default, ptr null
  store volatile ptr @def_fn_hidden, ptr null
  store volatile ptr @def_fn_hidden_linkonce_odr, ptr null
  store volatile ptr @def_fn_protected, ptr null
  ret void
}
