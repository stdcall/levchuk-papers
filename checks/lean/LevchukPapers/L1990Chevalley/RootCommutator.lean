import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.Module.Prod

namespace Levchuk1990Chevalley

/-- The quadratic ideal J₂ in lemma 7. -/
def quadraticDeviationIdeal (R : Type*) [CommRing R] : Ideal R :=
  Ideal.span (Set.range fun t : R => t ^ 2 - t)

/-- The two commuting root coordinates of [x εᵢ₁,y ε₁,₋₁].
Allowing all y gives the R-span of (t,t²). This models only that
commutator subgroup, not the other root coordinates or central series. -/
def rootCommutatorSpan (R : Type*) [CommRing R] : Submodule R (R × R) :=
  Submodule.span R (Set.range fun t : R => (t, t ^ 2))

private theorem diagonal_mem {R : Type*} [CommRing R] (a : R) :
    (a, a) ∈ rootCommutatorSpan R := by
  have h : ((1 : R), (1 : R)) ∈ rootCommutatorSpan R := by
    apply Submodule.subset_span
    exact ⟨1, by simp⟩
  simpa using (rootCommutatorSpan R).smul_mem a h

private theorem deviation_mem {R : Type*} [CommRing R] (t : R) :
    (t ^ 2 - t, 0) ∈ rootCommutatorSpan R := by
  have ht : (t, t ^ 2) ∈ rootCommutatorSpan R :=
    Submodule.subset_span ⟨t, rfl⟩
  have hd := diagonal_mem (t ^ 2)
  simpa using (rootCommutatorSpan R).sub_mem hd ht

private theorem ideal_coordinate_mem {R : Type*} [CommRing R] (z : R)
    (hz : z ∈ quadraticDeviationIdeal R) :
    (z, 0) ∈ rootCommutatorSpan R := by
  change z ∈ Submodule.span R (Set.range fun t : R => t ^ 2 - t) at hz
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
  · intro x hx
    rcases hx with ⟨t, rfl⟩
    exact deviation_mem t
  · exact (rootCommutatorSpan R).zero_mem
  · intro x y _ _ hx hy
    simpa using (rootCommutatorSpan R).add_mem hx hy
  · intro a x _ hx
    simpa using (rootCommutatorSpan R).smul_mem a hx

/-- The commutator coordinates are exactly K(1,1)+J₂(1,0).
All characteristics and zero divisors are allowed. This establishes
the coordinate constraint used in lemma 7; it does not prove the full
formula for Γᵢ or the classification of characteristic subgroups. -/
theorem rootCommutatorSpan_mem_iff {R : Type*} [CommRing R] (p : R × R) :
    p ∈ rootCommutatorSpan R ↔ p.1 - p.2 ∈ quadraticDeviationIdeal R := by
  constructor
  · intro hp
    change p ∈ Submodule.span R (Set.range fun t : R => (t, t ^ 2)) at hp
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
    · intro x hx
      rcases hx with ⟨t, rfl⟩
      have ht : t ^ 2 - t ∈ quadraticDeviationIdeal R :=
        Submodule.subset_span ⟨t, rfl⟩
      simpa using (quadraticDeviationIdeal R).neg_mem ht
    · simp
    · intro x y _ _ hx hy
      change x.1 + y.1 - (x.2 + y.2) ∈ quadraticDeviationIdeal R
      convert (quadraticDeviationIdeal R).add_mem hx hy using 1
      ring
    · intro a x _ hx
      change a * x.1 - a * x.2 ∈ quadraticDeviationIdeal R
      convert (quadraticDeviationIdeal R).mul_mem_left a hx using 1
      ring
  · intro hp
    have hi := ideal_coordinate_mem (p.1 - p.2) hp
    have hd := diagonal_mem p.2
    convert (rootCommutatorSpan R).add_mem hi hd using 1
    ext <;> simp

#print axioms rootCommutatorSpan_mem_iff

end Levchuk1990Chevalley
