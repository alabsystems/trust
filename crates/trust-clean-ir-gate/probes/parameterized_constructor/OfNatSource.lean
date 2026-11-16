/- Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0 -/

/-!
Logical source prerequisite for parameterized constructor lowering.

`OfNat` has two parameters (the type and the literal index) and one field.
Both are uniform parameters in constructor metadata; neither `OfNat` nor
`Fin` has a separate inductive index. A literal index is not a stored payload.
Its index need not equal its stored value. `Fin` has one parameter and two
fields, one computational and one proof. These theorems preserve the original
dependent types and identify which source projection observes the payload.

This does not define a native layout, erase a source declaration, authenticate
captured metadata, or grant runtime/carrier/codegen admission. Header/count
obligations remain the existing `CICL.ConstructorCertificate` contracts in the
pinned Clean source, including `constructorCertificate_arity` and `_fields`.
-/
namespace ParameterizedConstructor

@[reducible] def makeNat (index payload : Nat) : OfNat Nat index :=
  @OfNat.mk Nat index payload

def readNat (index : Nat) (source : OfNat Nat index) : Nat :=
  @OfNat.ofNat Nat index source

theorem nat_payload (index payload : Nat) :
    readNat index (makeNat index payload) = payload := by rfl

theorem nat_reindex (first second payload : Nat) :
    readNat first (makeNat first payload) =
      readNat second (makeNat second payload) := by rfl

@[reducible] def make64 (index : Nat) (payload : UInt64) : OfNat UInt64 index :=
  @OfNat.mk UInt64 index payload

def read64 (index : Nat) (source : OfNat UInt64 index) : UInt64 :=
  @OfNat.ofNat UInt64 index source

theorem u64_payload (index : Nat) (payload : UInt64) :
    read64 index (make64 index payload) = payload := by rfl

theorem u64_reindex (first second : Nat) (payload : UInt64) :
    read64 first (make64 first payload) =
      read64 second (make64 second payload) := by rfl

theorem u64_observer (observe : UInt64 -> Nat) (index : Nat) (payload : UInt64) :
    observe (read64 index (make64 index payload)) = observe payload := by rfl

def makeFin (bound payload : Nat) (within : payload < bound) : Fin bound :=
  @Fin.mk bound payload within

theorem fin_payload (bound payload : Nat) (within : payload < bound) :
    (makeFin bound payload within).val = payload := by rfl

theorem fin_proof_irrelevance (bound payload : Nat)
    (first second : payload < bound) :
    makeFin bound payload first = makeFin bound payload second := by rfl

end ParameterizedConstructor
