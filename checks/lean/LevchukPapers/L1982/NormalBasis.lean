import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic.Group

/-!
Bounded identities used on printed p. 510 in the proof of theorem 1.
These do not establish the normal-basis theorem or abnormality.
-/

namespace LevchukPapers1982

variable {G Q : Type*} [Group G] [Group Q]

theorem mapped_three_factor_commutator (φ : G →* G) (a b c : G) :
    φ (a * b * c) * (a * b * c)⁻¹ =
      φ a * φ b * φ c * c⁻¹ * b⁻¹ * a⁻¹ := by
  simp only [map_mul]
  group

theorem commutator_product (φ : G →* G) (a y : G) :
    φ (a * y) * (a * y)⁻¹ =
      (φ a * a⁻¹) * (a * (φ y * y⁻¹) * a⁻¹) := by
  simp only [map_mul]
  group

theorem quotient_fixed_tail (φ : G →* G) (q : G →* Q) (a y : G)
    (fixed : q (φ y) = q y) :
    q (φ (a * y) * (a * y)⁻¹) = q (φ a * a⁻¹) := by
  simp only [map_mul, map_inv, fixed]
  group

end LevchukPapers1982

#print axioms LevchukPapers1982.mapped_three_factor_commutator
#print axioms LevchukPapers1982.commutator_product
#print axioms LevchukPapers1982.quotient_fixed_tail
