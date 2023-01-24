import Mathlib.Data.Set.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Fintype.Basic

class Matroid (E : Type _) extends Fintype E :=
  ( bases' : Set (Set E) )
  ( independents' : Set (Set E) )
  ( circuits' : Set (Set E))
  ( mem_independents_iff' : ∀ i, i ∈ independents' ↔ ∃ b ∈ bases', i ⊆ b )
  ( bases_nonempty' : bases'.Nonempty )
  ( circuits_eq' : ∀ c, c ∈ circuits' ↔ (c ∉ independents' ∧
    ∀ c', c' ∉ independents' → c' ⊆ c → c' = c))
  ( steinitz_exchange' : ∀ {B₁ B₂},
      B₁ ∈ bases' → B₂ ∈ bases' → ∀ {e : E},
      e ∈ B₁ \ B₂ → ∃ f ∈ B₂ \ B₁,
        (B₁ \ {e}) ∪ {f} ∈ bases' )

namespace Matroid

variable {E : Type _} [Matroid E]

/-- `bases` are maximal independent sets -/
def bases (E : Type _) [Matroid E] : Set (Set E) :=
  Matroid.bases'

theorem bases_nonempty (E : Type _) [Matroid E] : (bases E).Nonempty :=
  Matroid.bases_nonempty'

/-- `circuits` are minimal dependent sets -/
def circuits (E : Type _) [Matroid E] : Set (Set E) :=
  Matroid.circuits'

/-- `independents` are subsets of bases -/
def independents (E : Type _) [Matroid E] : Set (Set E) :=
  Matroid.independents'

theorem mem_circuits_iff_independents {c : Set E} : c ∈ circuits E ↔
    (c ∉ independents E ∧ ∀ c', c' ∉ independents E → c' ⊆ c → c' = c) :=
  Matroid.circuits_eq' c

theorem mem_independents_iff_bases {i : Set E} : i ∈ independents E ↔
    ∃ b ∈ bases E, i ⊆ b :=
  Matroid.mem_independents_iff' i

theorem steinitz_exchange : ∀ {B₁ B₂},
    B₁ ∈ bases E → B₂ ∈ bases E → ∀ {e : E},
    e ∈ (B₁ \ B₂) → ∃ f ∈ B₂ \ B₁, (B₁ \ {e}) ∪ {f} ∈ bases E :=
  Matroid.steinitz_exchange'

theorem mem_bases_iff_independents {b : Set E} : b ∈ bases E ↔
    (b ∈ independents E ∧ ∀ i ∈ independents E, b ⊆ i → b = i) := by
  simp only [mem_independents_iff_bases]
  constructor
  . refine' fun hb => ⟨⟨b, hb, Set.Subset.refl _⟩,
      fun b' ⟨b₂, hb₂⟩ hb' => _⟩
    by_contra heq
    have hbb₂ : b ≠ b₂ := by
      rintro rfl
      exact heq (Set.Subset.antisymm hb' hb₂.2)
    have hbb₂ : b ⊂ b₂ := Set.ssubset_iff_subset_ne.2 ⟨hb'.trans hb₂.2, hbb₂⟩
    rcases Set.exists_of_ssubset hbb₂ with ⟨e, he⟩
    rcases steinitz_exchange hb₂.1 hb he with ⟨f, hf, _⟩
    rw [Set.mem_diff] at hf
    exact hf.2 (hbb₂.subset hf.1)
  . rintro ⟨⟨b', hb'⟩, h⟩
    rw [h b' ⟨b', hb'.1, refl _⟩ hb'.2]
    exact hb'.1

theorem mem_circuits_iff_independents' {c : Set E} : c ∈ circuits E ↔
    (c ∉ independents E ∧ ∀ (i), i ⊂ c → i ∈ independents E) := by
  simp only [mem_circuits_iff_independents, @not_imp_comm (_ ∈ independents E), not_forall, exists_prop,
    and_imp, ssubset_iff_subset_ne, ne_eq]

theorem empty_mem_independents : ∅ ∈ independents E := by
  rcases bases_nonempty E with ⟨b, hb⟩
  exact mem_independents_iff_bases.2 ⟨b, hb, Set.empty_subset _⟩

theorem mem_independents_of_subset {i₁ i₂} (h : i₁ ⊆ i₂) (hi : i₂ ∈ independents E) :
    (i₁ ∈ independents E) :=
  let ⟨b, hb⟩ := mem_independents_iff_bases.1 hi
  mem_independents_iff_bases.2 ⟨b, hb.1, h.trans hb.2⟩

end Matroid