-- Copyright 2026 Andrew Yates | Apache-2.0
import C11HeaderExecution
/-! Preserved semantic collision regression; V3's actual602byte links remain
unchanged, but the generic renderer must not erase grouping. -/
namespace C11HeaderRendererControls
open C11HeaderAST C11HeaderExecution
 def left : Expr .boolean := .not (.and (.truth false) (.truth false))
 def right : Expr .boolean := .and (.not (.truth false)) (.truth false)
 theorem left_tokens : expressionTokens "o" left = ["!", "(", "false", "&&", "false", ")"] := by rfl
 theorem right_tokens : expressionTokens "o" right = ["!", "false", "&&", "false"] := by rfl
 theorem different_tokens : (expressionTokens "o" left == expressionTokens "o" right) = false := by rfl
 theorem left_true (machine : Machine) : evaluate left machine = .ok (true, machine) := by rfl
 theorem right_false (machine : Machine) : evaluate right machine = .ok (false, machine) := by rfl
 theorem right_grouping_retained :
   expressionTokens "o" (.and (.truth true) (.and (.truth false) (.truth true))) =
     ["true", "&&", "(", "false", "&&", "true", ")"] := by rfl
 theorem double_not_unparenthesized : expressionTokens "o" (.not (.not (.truth false))) =
   ["!", "!", "false"] := by rfl
end C11HeaderRendererControls
