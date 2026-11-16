; NOTE: Do not autogenerate
; SPDX-FileCopyrightText: 2025 Contributors to TPDE <https://tpde.org>
; SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

; RUN: tpde-lli %s | FileCheck %s

declare i32 @printf(ptr, ...)

@fmt = private constant [4 x i8] c"%f\0A\00", align 1
define internal void @print_f32(float %v) {
  %e = fpext float %v to double
  call void @print_f64(double %e)
  ret void
}
define internal void @print_f64(double %v) {
  %p = call i32 (ptr, ...) @printf(ptr @fmt, double %v)
  ret void
}

define i32 @main() {
; CHECK: 1.000000
  %pow_f32_1 = call float @llvm.pow.f32.i32(float 1.0, float 10.0)
  call void @print_f32(float %pow_f32_1)
; CHECK: 1024.000000
  %pow_f32_2 = call float @llvm.pow.f32.i32(float 2.0, float 10.0)
  call void @print_f32(float %pow_f32_2)
; CHECK: 32.000000
  %pow_f32_3 = call float @llvm.pow.f32.i32(float 2.0, float 5.0)
  call void @print_f32(float %pow_f32_3)

; CHECK: 1.000000
  %pow_f64_1 = call double @llvm.pow.f64.i32(double 1.0, double 10.0)
  call void @print_f64(double %pow_f64_1)
; CHECK: 1024.000000
  %pow_f64_2 = call double @llvm.pow.f64.i32(double 2.0, double 10.0)
  call void @print_f64(double %pow_f64_2)
; CHECK: 32.000000
  %pow_f64_3 = call double @llvm.pow.f64.i32(double 2.0, double 5.0)
  call void @print_f64(double %pow_f64_3)

; CHECK: 1.000000
  %powi_f32_1 = call float @llvm.powi.f32.i32(float 1.0, i32 10)
  call void @print_f32(float %powi_f32_1)
; CHECK: 1024.000000
  %powi_f32_2 = call float @llvm.powi.f32.i32(float 2.0, i32 10)
  call void @print_f32(float %powi_f32_2)
; CHECK: 32.000000
  %powi_f32_3 = call float @llvm.powi.f32.i32(float 2.0, i32 5)
  call void @print_f32(float %powi_f32_3)

; CHECK: 1.000000
  %powi_f64_1 = call double @llvm.powi.f64.i32(double 1.0, i32 10)
  call void @print_f64(double %powi_f64_1)
; CHECK: 1024.000000
  %powi_f64_2 = call double @llvm.powi.f64.i32(double 2.0, i32 10)
  call void @print_f64(double %powi_f64_2)
; CHECK: 32.000000
  %powi_f64_3 = call double @llvm.powi.f64.i32(double 2.0, i32 5)
  call void @print_f64(double %powi_f64_3)

; CHECK: 0.000000
  %sin_f32_1 = call float @llvm.sin(float 0.0)
  call void @print_f32(float %sin_f32_1)
; CHECK: 0.000000
  %sin_f64_1 = call double @llvm.sin(double 0.0)
  call void @print_f64(double %sin_f64_1)

; CHECK: 1.000000
  %cos_f32_1 = call float @llvm.cos(float 0.0)
  call void @print_f32(float %cos_f32_1)
; CHECK: 1.000000
  %cos_f64_1 = call double @llvm.cos(double 0.0)
  call void @print_f64(double %cos_f64_1)

; CHECK: 0.000000
  %log_f32_1 = call float @llvm.log(float 1.0)
  call void @print_f32(float %log_f32_1)
; CHECK: 0.000000
  %log_f64_1 = call double @llvm.log(double 1.0)
  call void @print_f64(double %log_f64_1)

; CHECK: 0.000000
  %log10_f32_1 = call float @llvm.log10(float 1.0)
  call void @print_f32(float %log10_f32_1)
; CHECK: 2.000000
  %log10_f32_2 = call float @llvm.log10(float 100.0)
  call void @print_f32(float %log10_f32_2)
; CHECK: 0.000000
  %log10_f64_1 = call double @llvm.log10(double 1.0)
  call void @print_f64(double %log10_f64_1)
; CHECK: 2.000000
  %log10_f64_2 = call double @llvm.log10(double 100.0)
  call void @print_f64(double %log10_f64_2)

; CHECK: 1.000000
  %exp_f32_1 = call float @llvm.exp(float 0.0)
  call void @print_f32(float %exp_f32_1)
; CHECK: 1.000000
  %exp_f64_1 = call double @llvm.exp(double 0.0)
  call void @print_f64(double %exp_f64_1)

; CHECK: 2.000000
  %rint_f32_1 = call float @llvm.rint(float 1.75)
  call void @print_f32(float %rint_f32_1)
; CHECK: 2.000000
  %rint_f64_1 = call double @llvm.rint(double 1.75)
  call void @print_f64(double %rint_f64_1)

  ret i32 0
}
