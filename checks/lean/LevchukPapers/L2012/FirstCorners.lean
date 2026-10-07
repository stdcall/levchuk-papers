import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-!
A bounded step of corrected Lemma 6.2 (p.114): injectivity of full
first-corner projections for UT(3,K). Canonical coordinates are (r,s,t)
in x_alpha1(r) x_alpha2(s) x_(alpha1+alpha2)(t). The quotient h^-1 g
has coordinates (r-r0,s-s0,t-t0+(r-r0)*s0). Closure under this quotient
is explicit; this file does not prove the general Lie-type classification.
-/

namespace LevchukPapers2012English

variable {K : Type*} [Ring K]

def quotient (g h : Fin 3 → K) : Fin 3 → K :=
  ![g 0 - h 0, g 1 - h 1, g 2 - h 2 + (g 0 - h 0) * h 1]

def leading (M : Set (Fin 3 → K)) (i : Fin 3) : Prop :=
  ∃ x ∈ M, x i ≠ 0 ∧ ∀ j : Fin 3, j.val < i.val → x j = 0

theorem restricted_coordinates_injective
    (M : Set (Fin 3 → K))
    (closed : ∀ g ∈ M, ∀ h ∈ M, quotient g h ∈ M)
    (g h : Fin 3 → K) (hg : g ∈ M) (hh : h ∈ M)
    (same : ∀ i, leading M i → g i = h i) : g = h := by
  have eq0 : g 0 = h 0 := by
    by_contra ne
    apply ne
    apply same 0
    refine ⟨quotient g h, closed g hg h hh, ?_, ?_⟩
    · simpa [quotient] using (sub_ne_zero.mpr ne)
    · intro j hj
      simp at hj
  have eq1 : g 1 = h 1 := by
    by_contra ne
    apply ne
    apply same 1
    refine ⟨quotient g h, closed g hg h hh, ?_, ?_⟩
    · simpa [quotient] using (sub_ne_zero.mpr ne)
    · intro j hj
      fin_cases j <;> simp_all [quotient]
  have eq2 : g 2 = h 2 := by
    by_contra ne
    apply ne
    apply same 2
    refine ⟨quotient g h, closed g hg h hh, ?_, ?_⟩
    · simpa [quotient, eq0] using (sub_ne_zero.mpr ne)
    · intro j hj
      fin_cases j <;> simp_all [quotient]
  funext i
  fin_cases i
  · exact eq0
  · exact eq1
  · exact eq2

end LevchukPapers2012English

#print axioms LevchukPapers2012English.restricted_coordinates_injective
