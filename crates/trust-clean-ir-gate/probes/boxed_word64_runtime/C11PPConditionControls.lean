import C11PPConditions
namespace C11PPConditions

theorem source_version_condition :
    decideSource { macros := [("__STDC_VERSION__", ["201112L"])] }
      "defined(__STDC_VERSION__) && __STDC_VERSION__ > 201710L" = some false := by rfl

theorem missing_cpp_condition : decideSource {} "!defined(__cplusplus)" = some true := by rfl

theorem definition_presence_is_not_value_truth :
    decideSource { macros := [("present", ["0"])] } "defined(present)" = some true := by rfl

theorem invalid_rhs_cannot_hide : decideSource {} "0 && unknown_function()" = none := by rfl

theorem unsupported_expansion_cannot_hide :
    decideSource { macros := [("bad", ["1", "+", "1"])] } "0 && bad" = none := by rfl

theorem recursive_macro_refused :
    decideSource { macros := [("cycle", ["cycle"])] } "cycle" = none := by rfl

theorem ambiguous_macro_refused :
    decideSource { macros := [("x", ["0"]), ("x", ["1"])] } "x" = none := by rfl

theorem oversized_constant_refused : decideSource {} "9223372036854775808L" = none := by rfl
theorem missing_defined_operand_refused : decideSource {} "defined" = none := by rfl

theorem mixed_long_suffix_refused : decideSource {} "1lL" = none := by rfl
theorem relational_precedes_equality : decideSource {} "2 != 1 < 1" = some true := by rfl
theorem reserved_operator_not_undefined_zero : decideSource {} "_Pragma" = none := by rfl

theorem reserved_operator_alias_refused :
    decideSource { macros := [("alias", ["_Pragma"])] } "alias" = none := by rfl
end C11PPConditions
