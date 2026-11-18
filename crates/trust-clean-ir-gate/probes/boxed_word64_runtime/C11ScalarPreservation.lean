-- Copyright 2026 Andrew Yates | Apache-2.0
import C11ScalarValues
namespace C11ScalarValues
open C11HeaderTyping
/-- Value-domain preservation for every accepted supported conversion, not
only the finite controls. No C source execution, target or rights is assumed. -/
theorem convert_valid (target : CType) (value result : Value)
    (accepted : convert target value = some result) : valid result = true := by
  cases original : valid value with
  | false => simp [convert, original] at accepted
  | true =>
      cases value <;> cases target <;> simp_all [convert, typeOf]
      all_goals subst result
      all_goals first | exact unsigned_modulo_valid _ | exact int_result_valid _ | rfl

end C11ScalarValues
