// Trust: regression test for rust-lang#82699
// Large enums (>127 variants) can generate suboptimal switch instructions
// because the discriminant type is wider than necessary. When discriminant
// values include negative numbers or span a range that fits in a smaller
// type, LLVM should narrow the switch operand for better jump table generation.
//
// This test demonstrates the pattern: a large enum where each variant maps
// to a distinct constant. LLVM should generate a jump table or lookup table,
// not a chain of comparisons.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>

//@ compile-flags: -Copt-level=3

#![crate_type = "lib"]

// A large C-like enum with 200 variants.
// Discriminant values 0..=199 fit in u8 but Rust uses isize by default.
#[allow(dead_code)]
#[repr(u8)]
pub enum BigEnum {
    V0, V1, V2, V3, V4, V5, V6, V7, V8, V9,
    V10, V11, V12, V13, V14, V15, V16, V17, V18, V19,
    V20, V21, V22, V23, V24, V25, V26, V27, V28, V29,
    V30, V31, V32, V33, V34, V35, V36, V37, V38, V39,
    V40, V41, V42, V43, V44, V45, V46, V47, V48, V49,
    V50, V51, V52, V53, V54, V55, V56, V57, V58, V59,
    V60, V61, V62, V63, V64, V65, V66, V67, V68, V69,
    V70, V71, V72, V73, V74, V75, V76, V77, V78, V79,
    V80, V81, V82, V83, V84, V85, V86, V87, V88, V89,
    V90, V91, V92, V93, V94, V95, V96, V97, V98, V99,
    V100, V101, V102, V103, V104, V105, V106, V107, V108, V109,
    V110, V111, V112, V113, V114, V115, V116, V117, V118, V119,
    V120, V121, V122, V123, V124, V125, V126, V127, V128, V129,
    V130, V131, V132, V133, V134, V135, V136, V137, V138, V139,
    V140, V141, V142, V143, V144, V145, V146, V147, V148, V149,
    V150, V151, V152, V153, V154, V155, V156, V157, V158, V159,
    V160, V161, V162, V163, V164, V165, V166, V167, V168, V169,
    V170, V171, V172, V173, V174, V175, V176, V177, V178, V179,
    V180, V181, V182, V183, V184, V185, V186, V187, V188, V189,
    V190, V191, V192, V193, V194, V195, V196, V197, V198, V199,
}

// CHECK-LABEL: define {{.*}} @big_enum_to_str(i8
// When optimized, LLVM should produce a lookup table or jump table,
// NOT a long chain of comparisons. The optimized lookup should operate
// on i8 (the repr type), not a wider integer.
// CHECK: icmp ult i8
// CHECK: zext {{(nneg )?}}i8
// CHECK: ptr @switch.table.big_enum_to_str
// CHECK-NOT: icmp eq i8 %{{.*}}, 100
#[no_mangle]
pub fn big_enum_to_str(e: BigEnum) -> &'static str {
    match e {
        BigEnum::V0 => "zero",
        BigEnum::V1 => "one",
        BigEnum::V2 => "two",
        BigEnum::V3 => "three",
        BigEnum::V4 => "four",
        BigEnum::V5 => "five",
        BigEnum::V6 => "six",
        BigEnum::V7 => "seven",
        BigEnum::V8 => "eight",
        BigEnum::V9 => "nine",
        _ => "other",
    }
}

// A signed-repr enum where negative discriminants force LLVM to use
// a wider type. This is the specific pattern from rust-lang#82699 where
// codegen quality degrades.
#[allow(dead_code)]
#[repr(i16)]
pub enum SignedBigEnum {
    Neg5 = -5,
    Neg4 = -4,
    Neg3 = -3,
    Neg2 = -2,
    Neg1 = -1,
    Zero = 0,
    Pos1 = 1,
    Pos2 = 2,
    Pos3 = 3,
    Pos4 = 4,
    Pos5 = 5,
}

// CHECK-LABEL: define {{.*}} @signed_enum_to_val(i16
// The lookup should use the repr type (i16) directly, not widen to i32/i64.
// CHECK: sext i16
// CHECK: ptr @switch.table.signed_enum_to_val
// CHECK-NOT: switch i32
// CHECK-NOT: switch i64
#[no_mangle]
pub fn signed_enum_to_val(e: SignedBigEnum) -> u32 {
    match e {
        SignedBigEnum::Neg5 => 100,
        SignedBigEnum::Neg4 => 101,
        SignedBigEnum::Neg3 => 102,
        SignedBigEnum::Neg2 => 103,
        SignedBigEnum::Neg1 => 104,
        SignedBigEnum::Zero => 200,
        SignedBigEnum::Pos1 => 201,
        SignedBigEnum::Pos2 => 202,
        SignedBigEnum::Pos3 => 203,
        SignedBigEnum::Pos4 => 204,
        SignedBigEnum::Pos5 => 205,
    }
}
