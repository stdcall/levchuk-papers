import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Field.Basic

namespace LevchukPapers.L2020.ExactEnvelope

variable {F : Type*} [Field F]

def zeroProduct (_ _ : F) : F := 0
def fieldProduct (x y : F) : F := x * y

theorem zero_bilinear (x y z c : F) :
    zeroProduct (x + y) z = zeroProduct x z + zeroProduct y z ∧
    zeroProduct x (y + z) = zeroProduct x y + zeroProduct x z ∧
    zeroProduct (c * x) y = c * zeroProduct x y ∧
    zeroProduct x (c * y) = c * zeroProduct x y := by
  simp [zeroProduct]

theorem field_bilinear (x y z c : F) :
    fieldProduct (x + y) z = fieldProduct x z + fieldProduct y z ∧
    fieldProduct x (y + z) = fieldProduct x y + fieldProduct x z ∧
    fieldProduct (c * x) y = c * fieldProduct x y ∧
    fieldProduct x (c * y) = c * fieldProduct x y := by
  simp [fieldProduct, add_mul, mul_add, mul_assoc, mul_left_comm]

theorem zero_associative (x y z : F) :
    zeroProduct (zeroProduct x y) z = zeroProduct x (zeroProduct y z) := rfl

theorem field_associative (x y z : F) :
    fieldProduct (fieldProduct x y) z = fieldProduct x (fieldProduct y z) :=
  mul_assoc x y z

theorem zero_commutator (x y : F) :
    zeroProduct x y - zeroProduct y x = 0 := by simp [zeroProduct]

theorem field_commutator (x y : F) :
    fieldProduct x y - fieldProduct y x = 0 := by
  simp [fieldProduct, mul_comm]

theorem not_linearly_multiplicatively_isomorphic :
    ¬ ∃ f : F ≃ₗ[F] F, ∀ x y : F,
      f (fieldProduct x y) = zeroProduct (f x) (f y) := by
  rintro ⟨f, hf⟩
  have h : f (1 : F) = f 0 := by
    simpa [fieldProduct, zeroProduct] using hf 1 1
  exact one_ne_zero (f.injective h)

theorem reverse_not_linearly_multiplicatively_isomorphic :
    ¬ ∃ f : F ≃ₗ[F] F, ∀ x y : F,
      f (zeroProduct x y) = fieldProduct (f x) (f y) := by
  rintro ⟨f, hf⟩
  obtain ⟨x, hx⟩ := f.surjective (1 : F)
  have h : (0 : F) = 1 := by
    simpa [zeroProduct, fieldProduct, hx] using hf x x
  exact zero_ne_one h

#print axioms zero_bilinear
#print axioms field_bilinear
#print axioms zero_associative
#print axioms field_associative
#print axioms zero_commutator
#print axioms field_commutator
#print axioms not_linearly_multiplicatively_isomorphic
#print axioms reverse_not_linearly_multiplicatively_isomorphic
end LevchukPapers.L2020.ExactEnvelope
