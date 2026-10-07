import Mathlib.Algebra.Ring.Basic

/- Lemma3, author manuscript section2: bounded annihilator-map steps.
   The ring need not be associative or unital. The square-zero hypothesis
   on zeta follows in the article from image(zeta) in Ann R subset R².
   These lemmas do not formalize the root-system classification. -/
namespace LevchukPapers2018

theorem annihilator_perturbation_preserves_product
    {R : Type*} [NonUnitalNonAssocRing R] (zeta : R →+ R)
    (left_ann : ∀ x y : R, zeta x * y = 0)
    (right_ann : ∀ x y : R, x * zeta y = 0)
    (vanishes_products : ∀ x y : R, zeta (x * y) = 0) :
    ∀ x y : R, x * y + zeta (x * y) = (x + zeta x) * (y + zeta y) := by
  intro x y
  rw [vanishes_products, add_zero, add_mul, mul_add, mul_add,
      right_ann, left_ann, left_ann, add_zero, zero_add, add_zero]

theorem annihilator_perturbation_inverse
    {R : Type*} [NonUnitalNonAssocRing R] (zeta : R →+ R)
    (square_zero : ∀ x : R, zeta (zeta x) = 0) :
    (∀ x : R, (x + zeta x) - zeta (x + zeta x) = x) ∧
    (∀ x : R, (x - zeta x) + zeta (x - zeta x) = x) := by
  constructor
  · intro x
    rw [map_add, square_zero, add_zero, add_sub_cancel_right]
  · intro x
    rw [map_sub, square_zero, sub_zero, sub_add_cancel]

end LevchukPapers2018

#print axioms LevchukPapers2018.annihilator_perturbation_preserves_product
#print axioms LevchukPapers2018.annihilator_perturbation_inverse
