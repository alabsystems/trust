-- Copyright 2026 Andrew Yates | Apache-2.0
import C11HeaderTyping

/-! C integer-token elaboration for the supported int32/unsigned-int32 slice.
Values are parsed from the actual spelling, never read from producer annotations.
Other C literal families/targets refuse; target/configuration authenticity is not
established here. -/
namespace C11HeaderLiterals
open C11HeaderTyping
private def decimalDigit (char : Char) : Option Nat :=
  if '0' ≤ char && char ≤ '9' then some (char.toNat - '0'.toNat) else none
private def hexDigit (char : Char) : Option Nat :=
  if '0' ≤ char && char ≤ '9' then some (char.toNat - '0'.toNat)
  else if 'a' ≤ char && char ≤ 'f' then some (char.toNat - 'a'.toNat + 10)
  else if 'A' ≤ char && char ≤ 'F' then some (char.toNat - 'A'.toNat + 10)
  else none
private def digits (base bound : Nat) (digit : Char → Option Nat) (input : List Char) : Option Nat := do
  if input.isEmpty then none else
    input.foldlM (fun value char => do
      let next := value * base + (← digit char)
      if next < bound then some next else none) 0

def parse (target : Target) (token : String) : Option Raw := do
  if target != int32Target then none else
  match token.toList with
  | '0' :: 'x' :: rest | '0' :: 'X' :: rest =>
      if rest.getLast? == some 'u' || rest.getLast? == some 'U' then
        return .unsigned (← digits 16 4294967296 hexDigit rest.dropLast)
      else none
  | chars =>
      -- Only 0 or a nonzero-leading decimal sequence is supported, not octal.
      if chars.length > 1 && chars.head? == some '0' then none
      else return .decimal (← digits 10 2147483648 decimalDigit chars)

theorem drop_cutoff_spelling : parse int32Target "0xE0000000u" = some (.unsigned 3758096384) := by rfl

theorem increment_cutoff_spelling : parse int32Target "0xF0000000u" = some (.unsigned 4026531840) := by rfl

theorem zero_is_int_literal : parse int32Target "0" = some (.decimal 0) := by rfl

theorem one_is_int_literal : parse int32Target "1" = some (.decimal 1) := by rfl

theorem changed_value_is_not_name_bound : parse int32Target "0x0000002Au" = some (.unsigned 42) := by rfl

theorem overflowing_unsigned_refused : parse int32Target "0x100000000u" = none := by rfl

theorem invalid_hex_refused : parse int32Target "0xG0000000u" = none := by rfl

theorem negative_or_expression_refused : parse int32Target "1-1" = none := by rfl

theorem incompatible_target_refused :
    parse { intBits := 16, unsignedIntBits := 16 } "0xE0000000u" = none := by rfl
end C11HeaderLiterals
