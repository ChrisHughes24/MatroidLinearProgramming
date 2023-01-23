import MatroidLinearProgramming.Matroid
import Mathlib.Data.Fintype.Basic
import Mathlib.GroupTheory.Perm.Basic

inductive WithZeroSign : Type
| Pos : WithZeroSign
| Zero : WithZeroSign
| Neg : WithZeroSign
deriving DecidableEq

instance : One WithZeroSign := ⟨WithZeroSign.Pos⟩
instance : Zero WithZeroSign := ⟨WithZeroSign.Zero⟩
instance : Neg WithZeroSign :=
  ⟨fun s => match s with
    | WithZeroSign.Pos => WithZeroSign.Neg
    | WithZeroSign.Zero => WithZeroSign.Zero
    | WithZeroSign.Neg => WithZeroSign.Pos⟩

instance : Mul WithZeroSign :=
  ⟨fun s₁ s₂ => match s₁, s₂ with
    | WithZeroSign.Zero, _ => WithZeroSign.Zero
    | _, WithZeroSign.Zero => WithZeroSign.Zero
    | WithZeroSign.Pos, x => x
    | x, WithZeroSign.Pos => x
    | WithZeroSign.Neg, WithZeroSign.Neg => WithZeroSign.Pos⟩

instance : Fintype WithZeroSign :=
  ⟨⟨[WithZeroSign.Pos, WithZeroSign.Zero, WithZeroSign.Neg], by decide⟩,
    by intro x; cases x <;> simp⟩

instance : Inhabited WithZeroSign := ⟨WithZeroSign.Zero⟩

instance : CommMonoid WithZeroSign :=
  { mul_assoc := by decide
    one_mul := by decide
    mul_one := by decide
    mul_comm := by decide }

def boolLE : WithZeroSign → WithZeroSign → Bool
  | _, WithZeroSign.Pos => true
  | x, WithZeroSign.Zero => x ≠ WithZeroSign.Pos
  | x, WithZeroSign.Neg => x = WithZeroSign.Neg

instance : LE WithZeroSign := ⟨fun s₁ s₂ => boolLE s₁ s₂⟩

instance : DecidableRel (fun s₁ s₂ : WithZeroSign => s₁ ≤ s₂) :=
  fun s₁ s₂ => decidable_of_iff (boolLE s₁ s₂) Iff.rfl

instance : LinearOrder WithZeroSign :=
{ le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
  le_total := by decide
  decidable_le := by infer_instance }

open Matroid

@[ext] structure SignedSet (E : Type _) :=
  ( toSet : Set E )
  ( sign : toSet → Units ℤ )

namespace SignedSet

instance : EmptyCollection (SignedSet E) := ⟨⟨∅, fun x => False.elim x.2⟩⟩
instance : InvolutiveNeg (SignedSet E) :=
  { neg := fun s => ⟨s.toSet, fun x => -s.sign x⟩
    neg_neg := fun x => by simp [SignedSet.ext_iff] }

instance : Coe (SignedSet E) (Set E) := ⟨fun s => s.toSet⟩
attribute [coe] SignedSet.toSet

instance : Membership E (SignedSet E) := ⟨fun x s => x ∈ s.toSet⟩

@[simp]
theorem coe_empty : (↑∅ : Set E) = ∅ := rfl

@[simp]
theorem coe_neg (s : SignedSet E) : (↑(-s) : Set E) = s := rfl

def pos (c : SignedSet E) : Set E :=
  { x : E | ∃ h : x ∈ c, c.sign ⟨x, h⟩ = 1 }

def neg (c : SignedSet E) : Set E :=
  { x : E | ∃ h : x ∈ c, c.sign ⟨x, h⟩ = -1 }

end SignedSet

class OrientedMatroid (E : Type _) :=
  ( circuits : Set (SignedSet E) )
  ( empty_not_mem : ∅ ∉ circuits )
  ( neg_mem : ∀ c, c ∈ circuits → -c ∈ circuits )
  ( subset : ∀ c₁ ∈ circuits, ∀ c₂ ∈ circuits, c₁.toSet ⊆ c₂.toSet →
    c₁ = c₂ ∨ c₁ = -c₂ )
  ( eliminate : ∀ c₁ ∈ circuits, ∀ c₂ ∈ circuits, c₁ ≠ -c₂ →
      ∀ e ∈ c₁.pos ∩ c₂.neg, ∃ c₃ ∈ circuits,
        c₃.pos ⊆ (c₁.pos ∪ c₂.pos) \ {e} ∧ c₃.neg ⊆ (c₁.neg ∪ c₂.neg) \ {e} )

