import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Fintype.Basic

class Matroid (E : Type _) [DecidableEq E] extends Fintype E :=
  ( bases' : Finset (Finset E) )
  ( independents' : Finset (Finset E) )
  ( circuits' : Finset (Finset E))
  ( mem_independents_iff' : ∀ i, i ∈ independents' ↔ ∃ b ∈ bases', i ⊆ b )
  ( bases_nonempty' : bases'.Nonempty )
  ( circuits_eq' : ∀ c, c ∈ circuits' ↔ (c ∉ independents' ∧
    ∀ c', c' ∉ independents' → c' ⊆ c → c' = c))
  ( steinitz_exchange' : ∀ {B₁ B₂},
      B₁ ∈ bases' → B₂ ∈ bases' → ∀ {e : E},
      e ∈ B₁ \ B₂ → ∃ f ∈ B₂ \ B₁,
        (B₁ ∪ {f}) \ {e} ∈ bases' )

namespace Matroid

variable {E : Type _} [DecidableEq E] [Matroid E]

/-- `bases` are maximal independent Finsets -/
def bases (E : Type _) [DecidableEq E] [Matroid E] : Finset (Finset E) :=
  Matroid.bases'

theorem bases_nonempty (E : Type _) [DecidableEq E] [Matroid E] : (bases E).Nonempty :=
  Matroid.bases_nonempty'

/-- `circuits` are minimal dependent Finsets -/
def circuits (E : Type _) [DecidableEq E] [Matroid E] : Finset (Finset E) :=
  Matroid.circuits'

/-- `independents` are subFinsets of bases -/
def independents (E : Type _) [DecidableEq E] [Matroid E] : Finset (Finset E) :=
  Matroid.independents'

theorem mem_circuits_iff_independents {c : Finset E} : c ∈ circuits E ↔
    (c ∉ independents E ∧ ∀ c', c' ∉ independents E → c' ⊆ c → c' = c) :=
  Matroid.circuits_eq' c

theorem mem_independents_iff_bases {i : Finset E} : i ∈ independents E ↔
    ∃ b ∈ bases E, i ⊆ b :=
  Matroid.mem_independents_iff' i

theorem steinitz_exchange : ∀ {B₁ B₂},
    B₁ ∈ bases E → B₂ ∈ bases E → ∀ {e : E},
    e ∈ (B₁ \ B₂) → ∃ f ∈ B₂ \ B₁, (B₁ ∪ {f}) \ {e} ∈ bases E :=
  Matroid.steinitz_exchange'

theorem mem_bases_iff_independents {b : Finset E} : b ∈ bases E ↔
    (b ∈ independents E ∧ ∀ i ∈ independents E, b ⊆ i → b = i) := by
  simp only [mem_independents_iff_bases]
  constructor
  . refine' fun hb => ⟨⟨b, hb, Finset.Subset.refl _⟩,
      fun b' ⟨b₂, hb₂⟩ hb' => _⟩
    by_contra heq
    have hbb₂ : b ≠ b₂ := by
      rintro rfl
      exact heq (Finset.Subset.antisymm hb' hb₂.2)
    have hbb₂ : b ⊂ b₂ := Finset.ssubset_iff_subset_ne.2 ⟨hb'.trans hb₂.2, hbb₂⟩
    rcases Finset.exists_of_ssubset hbb₂ with ⟨e, he⟩
    rcases steinitz_exchange hb₂.1 hb (by simpa using he) with ⟨f, hf, _⟩
    rw [Finset.mem_sdiff] at hf
    exact hf.2 (hbb₂.subset hf.1)
  . rintro ⟨⟨b', hb'⟩, h⟩
    rw [h b' ⟨b', hb'.1, refl _⟩ hb'.2]
    exact hb'.1

theorem mem_circuits_iff_independents' {c : Finset E} : c ∈ circuits E ↔
    (c ∉ independents E ∧ ∀ (i), i ⊂ c → i ∈ independents E) := by
  simp only [mem_circuits_iff_independents, @not_imp_comm (_ ∈ independents E), not_forall, exists_prop,
    and_imp, ssubset_iff_subset_ne, ne_eq]

theorem empty_mem_independents : ∅ ∈ independents E := by
  rcases bases_nonempty E with ⟨b, hb⟩
  exact mem_independents_iff_bases.2 ⟨b, hb, Finset.empty_subset _⟩

theorem mem_independents_of_subFinset {i₁ i₂} (h : i₁ ⊆ i₂) (hi : i₂ ∈ independents E) :
    (i₁ ∈ independents E) :=
  let ⟨b, hb⟩ := mem_independents_iff_bases.1 hi
  mem_independents_iff_bases.2 ⟨b, hb.1, h.trans hb.2⟩

open Finset

private theorem basis_card_aux (b₁ b₂ : Finset E) (h₁ : b₁ ∈ bases E)
    (h₂ : b₂ ∈ bases E) (hlt : Finset.card b₂ < Finset.card b₁) : False := by
  have : (b₁ \ b₂).Nonempty := by
    by_contra h
    have h : b₁ ⊆ b₂ := by simpa only [not_nonempty_iff_eq_empty, sdiff_eq_empty_iff_subset] using h
    exact not_le_of_lt hlt (card_le_of_subset h)
  rcases this with ⟨e, he⟩
  rcases steinitz_exchange h₁ h₂ he with ⟨f, hf, hb⟩
  simp only [mem_sdiff] at he hf
  have : Finset.card b₂ < Finset.card ((b₁ ∪ {f}) \ {e}) := by
    rw [card_sdiff, card_disjoint_union] <;> simp [hlt, hf.2, he.1]
  have _wf : card (((b₁ ∪ {f}) \ {e}) \ b₂) < card (b₁ \ b₂) := by
    apply card_lt_card
    simp only [mem_union, mem_singleton, ssubset_def, subset_iff, mem_sdiff, and_imp, not_forall, not_and,
      not_not, exists_prop, exists_and_left]
    aesop
  exact basis_card_aux _ _ hb h₂ this
termination_by basis_card_aux b₁ b₂ _ _ _ => Finset.card (b₁ \ b₂)

theorem basis_card {b₁ b₂ : Finset E}  (h₁ : b₁ ∈ bases E)
    (h₂ : b₂ ∈ bases E) : Finset.card b₁ = Finset.card b₂ :=
  match lt_trichotomy (Finset.card b₁) (Finset.card b₂) with
  | Or.inl hlt => (basis_card_aux b₂ b₁ h₂ h₁ hlt).elim
  | Or.inr (Or.inl heq) => heq
  | Or.inr (Or.inr hlt) => (basis_card_aux b₁ b₂ h₁ h₂ hlt).elim

end Matroid