import Mathlib.Algebra.Ring.Basic

/- Bounded steps from Levchuk1983, printed pp.67 and71.
The first lemma is the central-idempotent argument in Lemma4; its two
existence hypotheses express equality eR=Re, not centrality itself.
The second is the concluding argument of Lemma10. Neither proves the
classification of automorphisms of the unitriangular group. -/
namespace LevchukPapers1983

theorem central_of_equal_principal_sides {R : Type*} [Ring R] (e : R)
    (hid : e * e = e)
    (right_to_left : ∀ x : R, ∃ y : R, e * x = y * e)
    (left_to_right : ∀ x : R, ∃ z : R, x * e = e * z) :
    ∀ x : R, e * x = x * e := by
  intro x
  obtain ⟨y, hy⟩ := right_to_left x
  obtain ⟨z, hz⟩ := left_to_right x
  have h₁ : (e * x) * e = e * x := by
    rw [hy, mul_assoc, hid]
  have h₂ : e * (x * e) = x * e := by
    rw [hz, ← mul_assoc, hid]
  calc
    e * x = (e * x) * e := h₁.symm
    _ = e * (x * e) := mul_assoc e x e
    _ = x * e := h₂

theorem additive_adjoint_map_preserves_product
    {R S : Type*} [NonUnitalRing R] [NonUnitalRing S] (f : R → S)
    (additive : ∀ a b : R, f (a + b) = f a + f b)
    (adjoint : ∀ a b : R, f (a + b + a * b) = f a + f b + f a * f b) :
    ∀ a b : R, f (a * b) = f a * f b := by
  intro a b
  have h := adjoint a b
  rw [additive (a + b) (a * b), additive a b] at h
  exact add_left_cancel h

end LevchukPapers1983

#print axioms LevchukPapers1983.central_of_equal_principal_sides
#print axioms LevchukPapers1983.additive_adjoint_map_preserves_product
