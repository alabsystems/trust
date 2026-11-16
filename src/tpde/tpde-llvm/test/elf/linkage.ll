; NOTE: Do not autogenerate
; SPDX-FileCopyrightText: 2025 Contributors to TPDE <https://tpde.org>
; SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

; RUN: tpde-llc --target=x86_64 < %s | llvm-readelf -s - | FileCheck %s
; RUN: tpde-llc --target=aarch64 < %s | llvm-readelf -s - | FileCheck %s

; TODO: make sure globals with private linkage don't end up in symbol table
; COM: CHECK-NOT: def_fn_private
; COM: CHECK-NOT: def_glob_private
; COM: CHECK-NOT: def_glob_tls_private
; CHECK-DAG: FUNC    LOCAL  DEFAULT  {{[0-9]+}} def_fn_internal
; CHECK-DAG: OBJECT  LOCAL  DEFAULT  {{[0-9]+}} def_glob_internal
; CHECK-DAG: TLS     LOCAL  DEFAULT  {{[0-9]+}} def_glob_tls_internal
; CHECK-DAG: FUNC    GLOBAL DEFAULT  {{[0-9]+}} def_fn_external
; CHECK-DAG: FUNC    WEAK   DEFAULT  {{[0-9]+}} def_fn_linkonce
; CHECK-DAG: FUNC    WEAK   DEFAULT  {{[0-9]+}} def_fn_weak
; CHECK-DAG: FUNC    WEAK   DEFAULT  {{[0-9]+}} def_fn_linkonce_odr
; CHECK-DAG: FUNC    WEAK   DEFAULT  {{[0-9]+}} def_fn_weak_odr
; CHECK-DAG: FUNC    GLOBAL DEFAULT  {{[0-9]+}} use
; CHECK-DAG: NOTYPE  GLOBAL DEFAULT         UND dec_fn_external
; CHECK-DAG: NOTYPE  WEAK   DEFAULT         UND dec_fn_extern_weak
; CHECK-DAG: NOTYPE  GLOBAL DEFAULT         UND dec_glob_external
; CHECK-DAG: NOTYPE  WEAK   DEFAULT         UND dec_glob_extern_weak
; CHECK-DAG: OBJECT  GLOBAL DEFAULT  {{[0-9]+}} def_glob_external
; CHECK-DAG: OBJECT  WEAK   DEFAULT  {{[0-9]+}} def_glob_linkonce
; CHECK-DAG: OBJECT  WEAK   DEFAULT  {{[0-9]+}} def_glob_weak
; TODO: properly implement common symbols
; COM: CHECK-DAG: OBJECT  GLOBAL DEFAULT         COM def_glob_common
; CHECK-DAG: OBJECT  WEAK   DEFAULT  {{[0-9]+}} def_glob_linkonce_odr
; CHECK-DAG: OBJECT  WEAK   DEFAULT  {{[0-9]+}} def_glob_weak_odr
; CHECK-DAG: TLS     GLOBAL DEFAULT         UND dec_glob_tls_external
; CHECK-DAG: TLS     WEAK   DEFAULT         UND dec_glob_tls_extern_weak
; CHECK-DAG: TLS     GLOBAL DEFAULT         UND def_glob_tls_available_externally
; CHECK-DAG: TLS     GLOBAL DEFAULT  {{[0-9]+}} def_glob_tls_external
; CHECK-DAG: TLS     WEAK   DEFAULT  {{[0-9]+}} def_glob_tls_linkonce
; CHECK-DAG: TLS     WEAK   DEFAULT  {{[0-9]+}} def_glob_tls_weak
; Note: TLS common symbols are not common.
; CHECK-DAG: TLS     WEAK   DEFAULT  {{[0-9]+}} def_glob_tls_common
; CHECK-DAG: TLS     WEAK   DEFAULT  {{[0-9]+}} def_glob_tls_linkonce_odr
; CHECK-DAG: TLS     WEAK   DEFAULT  {{[0-9]+}} def_glob_tls_weak_odr

declare external void @dec_fn_external();
declare extern_weak void @dec_fn_extern_weak();

define external void @def_fn_external() { ret void }
define private void @def_fn_private() { ret void }
define internal void @def_fn_internal() { ret void }
define available_externally void @def_fn_available_externally() { ret void }
define linkonce void @def_fn_linkonce() { ret void }
define weak void @def_fn_weak() { ret void }
define linkonce_odr void @def_fn_linkonce_odr() { ret void }
define weak_odr void @def_fn_weak_odr() { ret void }

@dec_glob_external = external global i32, align 4
@dec_glob_extern_weak = extern_weak global i32, align 4

@def_glob_external = global i32 100, align 4
@def_glob_private = private global i32 100, align 4
@def_glob_internal = internal global i32 100, align 4
@def_glob_available_externally = available_externally global i32 100, align 4
@def_glob_linkonce = linkonce global i32 100, align 4
@def_glob_weak = weak global i32 100, align 4
@def_glob_common = common global i32 0, align 4
@def_glob_linkonce_odr = linkonce_odr global i32 100, align 4
@def_glob_weak_odr = weak_odr global i32 100, align 4

@dec_glob_tls_external = external thread_local global i32, align 4
@dec_glob_tls_extern_weak = extern_weak thread_local global i32, align 4

@def_glob_tls_external = thread_local global i32 100, align 4
@def_glob_tls_private = private thread_local global i32 100, align 4
@def_glob_tls_internal = internal thread_local global i32 100, align 4
@def_glob_tls_available_externally = available_externally thread_local global i32 100, align 4
@def_glob_tls_linkonce = linkonce thread_local global i32 100, align 4
@def_glob_tls_weak = weak thread_local global i32 100, align 4
@def_glob_tls_common = common thread_local global i32 0, align 4
@def_glob_tls_linkonce_odr = linkonce_odr thread_local global i32 100, align 4
@def_glob_tls_weak_odr = weak_odr thread_local global i32 100, align 4

; Ensure that all symbols end up in the symbol table.
define void @use() {
    store ptr @dec_fn_external, ptr null
    store ptr @dec_fn_extern_weak, ptr null
    store ptr @def_fn_external, ptr null
    store ptr @def_fn_private, ptr null
    store ptr @def_fn_internal, ptr null
    store ptr @def_fn_available_externally, ptr null
    store ptr @def_fn_linkonce, ptr null
    store ptr @def_fn_weak, ptr null
    store ptr @def_fn_linkonce_odr, ptr null
    store ptr @def_fn_weak_odr, ptr null
    store ptr @dec_glob_external, ptr null
    store ptr @dec_glob_extern_weak, ptr null
    store ptr @def_glob_external, ptr null
    store ptr @def_glob_private, ptr null
    store ptr @def_glob_internal, ptr null
    store ptr @def_glob_available_externally, ptr null
    store ptr @def_glob_linkonce, ptr null
    store ptr @def_glob_weak, ptr null
    store ptr @def_glob_common, ptr null
    store ptr @def_glob_linkonce_odr, ptr null
    store ptr @def_glob_weak_odr, ptr null

    %dec_glob_tls_external = call ptr @llvm.threadlocal.address(ptr @dec_glob_tls_external)
    store volatile ptr %dec_glob_tls_external, ptr null
    %dec_glob_tls_extern_weak = call ptr @llvm.threadlocal.address(ptr @dec_glob_tls_extern_weak)
    store volatile ptr %dec_glob_tls_extern_weak, ptr null
    %def_glob_tls_available_externally = call ptr @llvm.threadlocal.address(ptr @def_glob_tls_available_externally)
    store volatile ptr %def_glob_tls_available_externally, ptr null
    ret void
}
