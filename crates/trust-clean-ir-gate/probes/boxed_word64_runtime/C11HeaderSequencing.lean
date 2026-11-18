-- Copyright 2026 Andrew Yates | Apache-2.0
import C11HeaderAST

/-! The generic projection interpreter picks an operand order. C does not
sequence ordinary comparison/call operands. For the ACTUAL fragments the
addresses and converted literal/macro operands are atomic-effect-free, so no
extra atomic event ordering is being selected between two effectful operands.
This checked syntactic property is necessary only: it does not supply C scalar
conversion, object lifetime, actual macro expansion or full C11 adequacy. -/
namespace C11HeaderSequencing
open C11HeaderAST

def effectFree : {t : Ty} → Expr t → Bool
  | _, .argument | _, .word _ | _, .macro _ | _, .truth _ => true
  | _, .headerAddress object => effectFree object
  | _, .scalar object => effectFree object
  | _, .load _ | _, .fetchAdd .. | _, .fetchSub .. => false
  | _, .ge a b | _, .lt a b | _, .ne a b => effectFree a && effectFree b
  | _, .not a => effectFree a
  | _, .and a b => effectFree a && effectFree b

def safeExpression : {t : Ty} → Expr t → Bool
  | _, .argument | _, .word _ | _, .macro _ | _, .truth _ => true
  | _, .headerAddress object => safeExpression object
  | _, .scalar object => safeExpression object
  | _, .load pointer => effectFree pointer
  | _, .fetchAdd pointer value _ | _, .fetchSub pointer value _ =>
      effectFree pointer && effectFree value
  | _, .ge a b | _, .lt a b | _, .ne a b =>
      safeExpression a && safeExpression b && (effectFree a || effectFree b)
  | _, .not a => safeExpression a
  | _, .and a b => safeExpression a && safeExpression b

def safeStatement : Stmt t → Bool
  | .skip | .fence _ => true
  | .block body => safeStatement body
  | .sequence a b => safeStatement a && safeStatement b
  | .branch condition yes no => safeExpression condition && safeStatement yes && safeStatement no
  | .expression e => safeExpression e
  | .ret e => safeExpression e

theorem actual_drop_sequencing (limit : String) : safeStatement (drop limit) = true := by rfl

theorem actual_increment_sequencing (limit : String) : safeStatement (increment limit) = true := by rfl

/-- A generalized expression with two atomic comparison operands is outside
this supported source-order slice, even though the typed projection can run it. -/
theorem two_atomic_comparison_operands_refused :
    safeExpression (.ne (.load address) (.load address)) = false := by rfl

/-- Atomic call arguments cannot hide another unsequenced atomic access. -/
theorem atomic_operand_in_rmw_refused :
    safeExpression (.fetchSub address (.load address) .release) = false := by rfl

/-- && DOES sequence its two evaluations, so two separately safe conditions
are supported; no artificial cross-operand ordering rejection is added. -/
theorem short_circuit_two_loads_supported :
    safeExpression (.and (.lt (.load address) (.word 4))
      (.ne (.load address) (.word 0))) = true := by rfl

#print axioms actual_drop_sequencing
#print axioms two_atomic_comparison_operands_refused
end C11HeaderSequencing
