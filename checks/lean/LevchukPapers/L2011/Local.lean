import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Group.Hom.Defs

/- Limited universal steps for the 2011 article. These do not formalize
   the Chevalley classification or the full local-map theorems. -/
namespace LevchukPapers2011Local

theorem conjugation_witness {R : Type*} [Ring R]
    (a b : R) (h : b * a * b = 0) :
    (1 - b) * a * (1 + b) = a + (a * b - b * a) := by
  calc
    (1 - b) * a * (1 + b) = a + (a * b - b * a) - b * a * b := by
      noncomm_ring
    _ = a + (a * b - b * a) := by rw [h]; simp

theorem square_zero_inverse {R : Type*} [Ring R]
    (b : R) (h : b * b = 0) : (1 - b) * (1 + b) = 1 := by
  calc
    (1 - b) * (1 + b) = 1 - b * b := by noncomm_ring
    _ = 1 := by rw [h]; simp

theorem derived_functional_obstruction
    {L A : Type*} [AddCommGroup L] [AddCommGroup A]
    (bracket : L → L → L) (D : L →+ L) (ell : L →+ A)
    (hD : ∀ x y, D (bracket x y) = bracket (D x) y + bracket x (D y))
    (hzero : ∀ x y, ell (bracket x y) = 0) (u v : L) :
    ell (D (bracket u v)) = 0 := by
  rw [hD, map_add, hzero, hzero, add_zero]

theorem idempotent_outer_sum_minor {K : Type*} [CommRing K]
    (f u₁ u₂ v₁ v₂ x₁ x₂ y₁ y₂ : K) (h : f * (1 - f) = 0) :
    (f * u₁ * v₁ + (1 - f) * x₁ * y₁) *
      (f * u₂ * v₂ + (1 - f) * x₂ * y₂) -
    (f * u₁ * v₂ + (1 - f) * x₁ * y₂) *
      (f * u₂ * v₁ + (1 - f) * x₂ * y₁) = 0 := by
  calc
    _ = f * (1 - f) *
      (u₁ * v₁ * x₂ * y₂ + x₁ * y₁ * u₂ * v₂ -
        u₁ * v₂ * x₂ * y₁ - x₁ * y₂ * u₂ * v₁) := by ring
    _ = 0 := by rw [h, zero_mul]

theorem paired_target_minor_forces_zero {K : Type*} [CommRing K]
    (t : K) (h : (1 : K) * 0 - 1 * t = 0) : t = 0 := by
  simpa using h

end LevchukPapers2011Local

#print axioms LevchukPapers2011Local.conjugation_witness
#print axioms LevchukPapers2011Local.square_zero_inverse
#print axioms LevchukPapers2011Local.derived_functional_obstruction
#print axioms LevchukPapers2011Local.idempotent_outer_sum_minor
#print axioms LevchukPapers2011Local.paired_target_minor_forces_zero
