import Mathlib.Data.Fin.Basic

/- def:l2015-exceptional-proper: coordinate fullness is equivalent to
   absence of a coordinate which vanishes on the entire subgroup.
   These bounded lemmas do not count subspaces or classify ideals. -/
namespace LevchukPapers2015Exceptional

theorem coordinate_full_iff
    {m : ℕ} {K : Type*} [Zero K] (S : Set (Fin m → K)) :
    (∀ i : Fin m, ∃ v ∈ S, v i ≠ 0) ↔
    (∀ i : Fin m, ¬ ∀ v ∈ S, v i = 0) := by
  constructor
  · intro h i hz
    obtain ⟨v, hv, hn⟩ := h i
    exact hn (hz v hv)
  · intro h i
    classical
    by_contra hn
    apply h i
    intro v hv
    by_contra hz
    exact hn ⟨v, hv, hz⟩

theorem last_coordinate_is_required
    {m : ℕ} {K : Type*} [Zero K] (S : Set (Fin (m+1) → K))
    (h : ∀ i : Fin (m+1), ∃ v ∈ S, v i ≠ 0) :
    ∃ v ∈ S, v (Fin.last m) ≠ 0 := h (Fin.last m)

theorem coordinate_full_has_nonzero_vector
    {m : ℕ} {K : Type*} [Zero K] (S : Set (Fin (m+1) → K))
    (h : ∀ i : Fin (m+1), ∃ v ∈ S, v i ≠ 0) :
    ∃ v ∈ S, v ≠ (fun _ => 0) := by
  obtain ⟨v, hv, hn⟩ := h (Fin.last m)
  refine ⟨v, hv, ?_⟩
  intro hz
  apply hn
  rw [hz]

end LevchukPapers2015Exceptional

#print axioms LevchukPapers2015Exceptional.coordinate_full_iff
#print axioms LevchukPapers2015Exceptional.last_coordinate_is_required
#print axioms LevchukPapers2015Exceptional.coordinate_full_has_nonzero_vector
