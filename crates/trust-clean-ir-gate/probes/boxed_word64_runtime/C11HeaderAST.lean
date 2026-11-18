-- Copyright 2026 Andrew Yates | Apache-2.0
import C11ActualTokens
import C11ActualFragmentPhases

/-! A typed, restricted C fragment AST. The intrinsic/field constructors below
are a RESOLVED proposal, not resolution of C macro names or typedefs from a TU.
The independent concrete token equation retains the unresolved binding obligation.
No source rights, layout, atomic adequacy or code-generation authority follows. -/
namespace C11HeaderAST
inductive Ty where
  | u32 | boolean | atomicPtr | objectPtr | unit
  deriving DecidableEq, Repr
inductive Order where
  | relaxed | release | acquire
  deriving DecidableEq, Repr
inductive Expr : Ty → Type where
  | argument : Expr .objectPtr
  | headerAddress : Expr .objectPtr → Expr .atomicPtr
  | scalar : Expr .objectPtr → Expr .boolean
  | word : UInt32 → Expr .u32
  | macro : String → Expr .u32
  | truth : Bool → Expr .boolean
  | load : Expr .atomicPtr → Expr .u32
  | fetchAdd : Expr .atomicPtr → Expr .u32 → Order → Expr .u32
  | fetchSub : Expr .atomicPtr → Expr .u32 → Order → Expr .u32
  | ge : Expr .u32 → Expr .u32 → Expr .boolean
  | lt : Expr .u32 → Expr .u32 → Expr .boolean
  | ne : Expr .u32 → Expr .u32 → Expr .boolean
  | not : Expr .boolean → Expr .boolean
  | and : Expr .boolean → Expr .boolean → Expr .boolean
inductive Stmt (result : Ty) where
  | skip : Stmt result
  | block : Stmt result → Stmt result
  | sequence : Stmt result → Stmt result → Stmt result
  | branch : Expr .boolean → Stmt result → Stmt result → Stmt result
  | expression : Expr .u32 → Stmt result
  | fence : Order → Stmt result
  | ret : Expr result → Stmt result

def address : Expr .atomicPtr := .headerAddress .argument
/-- The threshold value is supplied only AFTER a separate TU/macro binding.
No claim that an arbitrary supplied value is CLEAN_RC_STICKY_DROP. -/
def drop (threshold : String) : Stmt .boolean :=
  .sequence (.branch (.ge (.load address) (.macro threshold))
    (.ret (.truth false)) .skip)
    (.sequence (.branch (.ne (.fetchSub address (.word 1) .release) (.word 0))
      (.ret (.truth false)) .skip)
      (.sequence (.fence .acquire) (.ret (.truth true))))
def increment (threshold : String) : Stmt .unit :=
  .branch (.and (.not (.scalar .argument))
    (.lt (.load address) (.macro threshold)))
    (.block (.expression (.fetchAdd address (.word 1) .relaxed))) .skip

/-- Ordinary syntax rendering keeps the actual names, fields, qualifiers,
short-circuit operator and all statements. Intrinsic roles still owe TU binding. -/
def orderTokens : Order → String
  | .relaxed => "memory_order_relaxed"
  | .release => "memory_order_release"
  | .acquire => "memory_order_acquire"
/-- C precedence, with explicit parentheses whenever the surrounding context
would parse a different tree. Right operands use a stricter context to retain
left-associative grouping. This preserves the original two source renderings. -/
def precedence : {t : Ty} → Expr t → Nat
  | _, .and .. => 5
  | _, .ne .. => 9
  | _, .ge .. | _, .lt .. => 10
  | _, .not .. | _, .headerAddress .. => 14
  | _, _ => 15

def expressionTokensAt (context : Nat) (arg : String) : {t : Ty} → Expr t → List String
  | _, expression =>
    let body := match expression with
      | .argument => [arg]
      | .headerAddress e => ["&"] ++ expressionTokensAt 15 arg e ++ ["->", "header", ".", "ref_count"]
      | .scalar e => ["clean_is_scalar", "("] ++ expressionTokensAt 0 arg e ++ [")"]
      | .word value => [toString value.toNat]
      | .macro name => [name]
      | .truth value => [if value then "true" else "false"]
      | .load pointer => ["atomic_load_explicit", "("] ++ expressionTokensAt 0 arg pointer ++
          [",", "memory_order_relaxed", ")"]
      | .fetchAdd pointer value order => ["atomic_fetch_add_explicit", "("] ++
          expressionTokensAt 0 arg pointer ++ [","] ++ expressionTokensAt 0 arg value ++ [",", orderTokens order, ")"]
      | .fetchSub pointer value order => ["atomic_fetch_sub_explicit", "("] ++
          expressionTokensAt 0 arg pointer ++ [","] ++ expressionTokensAt 0 arg value ++ [",", orderTokens order, ")"]
      | .ge a b => expressionTokensAt 10 arg a ++ [">="] ++ expressionTokensAt 11 arg b
      | .lt a b => expressionTokensAt 10 arg a ++ ["<"] ++ expressionTokensAt 11 arg b
      | .ne a b => expressionTokensAt 9 arg a ++ ["!="] ++ expressionTokensAt 10 arg b
      | .not a => ["!"] ++ expressionTokensAt 14 arg a
      | .and a b => expressionTokensAt 5 arg a ++ ["&&"] ++ expressionTokensAt 6 arg b
    if precedence expression < context then ["("] ++ body ++ [")"] else body

def expressionTokens (arg : String) (expression : Expr t) : List String :=
  expressionTokensAt 0 arg expression

def statementTokens (arg : String) : Stmt t → List String
  | .skip => []
  | .block a => ["{"] ++ statementTokens arg a ++ ["}"]
  | .sequence a b => statementTokens arg a ++ statementTokens arg b
  | .branch condition yes .skip => ["if", "("] ++ expressionTokens arg condition ++
      [")"] ++ statementTokens arg yes
  | .branch condition yes no => ["if", "("] ++ expressionTokens arg condition ++
      [")"] ++ statementTokens arg yes ++ ["else"] ++ statementTokens arg no
  | .expression e => expressionTokens arg e ++ [";"]
  | .fence order => ["atomic_thread_fence", "(", orderTokens order, ")", ";"]
  | .ret e => ["return"] ++ expressionTokens arg e ++ [";"]

def functionTokens (result : String) (names : CAtomicDropSyntax.Proposal)
    (body : Stmt t) : List String :=
  ["static", "inline", result, names.functionName, "(", "clean_obj", "*", names.argument,
    ")", "{"] ++ statementTokens names.argument body ++ ["}"]

theorem drop_render_exact (p : CAtomicDropSyntax.Proposal) :
    functionTokens "bool" p (drop p.thresholdMacro) = CAtomicDropSyntax.tokens p := by rfl

theorem increment_render_exact (p : CAtomicDropSyntax.Proposal) :
    functionTokens "void" p (increment p.thresholdMacro) = CAtomicIncrementSyntax.tokens p := by rfl

theorem actual_drop_ast_tokens :
    C11OrdinaryTokens.Lexes CAtomicDropSource.actualSource
      (functionTokens "bool" CAtomicDropSource.proposal (drop CAtomicDropSource.proposal.thresholdMacro)) := by
  rw [drop_render_exact]
  exact C11ActualTokens.drop_actual_lexes

theorem actual_increment_ast_tokens :
    C11OrdinaryTokens.Lexes CAtomicIncrementSource.actualSource
      (functionTokens "void" CAtomicIncrementSource.proposal (increment CAtomicIncrementSource.proposal.thresholdMacro)) := by
  rw [increment_render_exact]
  exact C11ActualTokens.increment_actual_lexes
/-- The exact original bytes also have this AST rendering after the separately
proved mechanical phase1/2 identity; no full-TU preprocessing is inferred. -/
theorem actual_drop_after_phases :
    C11OrdinaryTokens.Lexes
      (C11FragmentPhases.mechanical12 CAtomicDropSource.actualSource)
      (functionTokens "bool" CAtomicDropSource.proposal (drop CAtomicDropSource.proposal.thresholdMacro)) := by
  rw [C11ActualFragmentPhases.drop_phase12_identity]
  exact actual_drop_ast_tokens

theorem actual_increment_after_phases :
    C11OrdinaryTokens.Lexes
      (C11FragmentPhases.mechanical12 CAtomicIncrementSource.actualSource)
      (functionTokens "void" CAtomicIncrementSource.proposal (increment CAtomicIncrementSource.proposal.thresholdMacro)) := by
  rw [C11ActualFragmentPhases.increment_phase12_identity]
  exact actual_increment_ast_tokens

end C11HeaderAST
