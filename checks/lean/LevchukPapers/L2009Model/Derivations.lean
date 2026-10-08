import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Abel

/- Lemma 1, printed p.185: ζ is an additive endomorphism and ζ(R)^2=0.
The latter means that every product of two image elements is zero;
it does not mean merely ζ ∘ ζ = 0. No identity, commutativity, nonzero
ring, matrix rank, or characteristic assumption is needed for this step.
The checked passage is lem:l2009-model-square-zero-derivation.
This proves the derivation/multiplicativity equivalence, not any subsequent
classification of derivations or elementary-equivalence theorem. -/
namespace LevchukPapers.L2009Model

def perturbation {R : Type*} [NonUnitalRing R] (ζ : R →+ R) (x : R) : R :=
  x + ζ x

theorem perturbation_add {R : Type*} [NonUnitalRing R] (ζ : R →+ R)
    (a b : R) : perturbation ζ (a + b) = perturbation ζ a + perturbation ζ b := by
  simp only [perturbation, map_add]
  abel

theorem derivation_iff_perturbation_multiplicative
    {R : Type*} [NonUnitalRing R] (ζ : R →+ R)
    (image_square_zero : ∀ a b : R, ζ a * ζ b = 0) :
    (∀ a b : R, ζ (a * b) = ζ a * b + a * ζ b) ↔
      (∀ a b : R, perturbation ζ (a * b) =
        perturbation ζ a * perturbation ζ b) := by
  have expand (a b : R) :
      (a + ζ a) * (b + ζ b) = a * b + (ζ a * b + a * ζ b) := by
    simp only [add_mul, mul_add, image_square_zero, add_zero]
    abel
  constructor
  · intro derivation a b
    change a * b + ζ (a * b) = (a + ζ a) * (b + ζ b)
    rw [expand, derivation a b]
  · intro multiplicative a b
    have h := multiplicative a b
    change a * b + ζ (a * b) = (a + ζ a) * (b + ζ b) at h
    rw [expand] at h
    exact add_left_cancel h

end LevchukPapers.L2009Model

#print axioms LevchukPapers.L2009Model.perturbation_add
#print axioms LevchukPapers.L2009Model.derivation_iff_perturbation_multiplicative
