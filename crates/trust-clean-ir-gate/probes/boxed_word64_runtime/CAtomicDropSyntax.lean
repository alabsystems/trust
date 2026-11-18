-- Copyright 2026 Andrew Yates | Apache-2.0
import Init

/-!
Total incremental ASCII C-fragment lexer. Exact bytes, comments and all tokens
are consumed; unsupported syntax and incomplete comments/operators refuse.
This establishes only lexical/complete-shape facts, not full TU preprocessing,
C typing/layout, C11 execution or ARC/NoUB correspondence. Checked intermediate
states are proof cuts, not trusted lexer advice.
-/
namespace CAtomicDropSyntax
inductive Mode where
  | normal | ident | slash | line | block | star | greater | less | bang | dash | amp
  deriving DecidableEq, Repr
structure State where
  mode : Mode := .normal
  word : List UInt8 := []
  reversed : List String := []
  deriving DecidableEq, Repr

def initial : State := {}
private def letter (b : UInt8) : Bool :=
  (97 ≤ b.toNat && b.toNat ≤ 122) || (65 ≤ b.toNat && b.toNat ≤ 90) || b == 95
private def digit (b : UInt8) : Bool := 48 ≤ b.toNat && b.toNat ≤ 57
private def rest (b : UInt8) : Bool := letter b || digit b
private def white (b : UInt8) : Bool :=
  b == 32 || b == 9 || b == 10 || b == 11 || b == 12 || b == 13
private def text (bs : List UInt8) : String :=
  String.ofList (bs.map (fun b => Char.ofNat b.toNat))
private def emit (s : State) (token : String) : State :=
  { mode := .normal, word := [], reversed := token :: s.reversed }
private def normal (s : State) (b : UInt8) : Option State :=
  if white b then some s
  else if letter b || digit b then some { s with mode := .ident, word := [b] }
  else if b == 47 then some { s with mode := .slash }
  else if b == 62 then some { s with mode := .greater }
  else if b == 60 then some { s with mode := .less }
  else if b == 38 then some { s with mode := .amp }
  else if b == 33 then some { s with mode := .bang }
  else if b == 45 then some { s with mode := .dash }
  else if b == 40 || b == 41 || b == 123 || b == 125 || b == 42 ||
      b == 46 || b == 44 || b == 59 then some (emit s (text [b]))
  else none

def step (s : State) (b : UInt8) : Option State :=
  -- Restrict the raw-source phase: no line splicing, trigraphs, CR mapping,
  -- NUL or non-ASCII inputs. Those need a checked C translation-phase owner.
  if b == 92 || b == 63 || !(b == 9 || b == 10 || (32 ≤ b.toNat && b.toNat ≤ 126)) then none
  else match s.mode with
  | .normal => normal s b
  | .ident => if rest b then some { s with word := b :: s.word }
      else normal (emit s (text s.word.reverse)) b
  | .slash => if b == 47 then some { s with mode := .line }
      else if b == 42 then some { s with mode := .block } else none
  | .line => some { s with mode := if b == 10 then .normal else .line }
  | .block => some { s with mode := if b == 42 then .star else .block }
  | .star => some { s with mode := if b == 47 then .normal else if b == 42 then .star else .block }
  | .greater => if b == 61 then some (emit s ">=") else normal (emit s ">") b
  | .less => if b == 61 then some (emit s "<=") else normal (emit s "<") b
  | .amp => if b == 38 then some (emit s "&&") else normal (emit s "&") b
  | .bang => if b == 61 then some (emit s "!=") else normal (emit s "!") b
  | .dash => if b == 62 then some (emit s "->") else none

def feed (state : Option State) (bytes : List UInt8) : Option State :=
  bytes.foldl (fun st b => st.bind (fun s => step s b)) state

def finish (s : State) : Option (List String) :=
  match s.mode with
  | .normal | .line => some s.reversed.reverse
  | .ident => some ((emit s (text s.word.reverse)).reversed.reverse)
  | .greater => some ((emit s ">").reversed.reverse)
  | .less => some ((emit s "<").reversed.reverse)
  | .bang => some ((emit s "!").reversed.reverse)
  | .amp => some ((emit s "&").reversed.reverse)
  | _ => none

def tokenize (source : List UInt8) : Option (List String) :=
  (feed (some initial) source).bind finish

def tokenizeChunks (chunks : List (List UInt8)) : Option (List String) :=
  (chunks.foldl feed (some initial)).bind finish

theorem feed_append (s : Option State) (a b : List UInt8) :
    feed s (a ++ b) = feed (feed s a) b := by
  exact List.foldl_append

theorem feed_chunks (chunks : List (List UInt8)) (s : Option State) :
    chunks.foldl feed s = feed s chunks.flatten := by
  induction chunks generalizing s with
  | nil => rfl
  | cons a tail ih =>
    simp only [List.foldl_cons, List.flatten_cons]
    rw [ih, feed_append]

theorem chunks_exact (chunks : List (List UInt8)) :
    tokenizeChunks chunks = tokenize chunks.flatten := by
  unfold tokenizeChunks tokenize
  rw [feed_chunks]

structure Proposal where
  functionName : String
  argument : String
  thresholdMacro : String
  deriving DecidableEq, Repr
private def address (p : Proposal) : List String :=
  ["&", p.argument, "->", "header", ".", "ref_count"]
def tokens (p : Proposal) : List String :=
  ["static", "inline", "bool", p.functionName, "(", "clean_obj", "*", p.argument,
   ")", "{", "if", "(", "atomic_load_explicit", "("] ++ address p ++
  [",", "memory_order_relaxed", ")", ">=", p.thresholdMacro, ")", "return", "false", ";",
   "if", "(", "atomic_fetch_sub_explicit", "("] ++ address p ++
  [",", "1", ",", "memory_order_release", ")", "!=", "0", ")", "return", "false", ";",
   "atomic_thread_fence", "(", "memory_order_acquire", ")", ";", "return", "true", ";", "}"]
def check (source : List UInt8) (proposal : Proposal) : Bool :=
  decide (tokenize source = some (tokens proposal))
theorem check_sound (source : List UInt8) (proposal : Proposal)
    (accepted : check source proposal = true) :
    tokenize source = some (tokens proposal) := of_decide_eq_true accepted

#print axioms feed_chunks
#print axioms chunks_exact
#print axioms check_sound
end CAtomicDropSyntax
