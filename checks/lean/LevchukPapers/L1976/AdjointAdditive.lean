import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NoncommRing

/-!
The passage `pass:adjoint-additive-closure` proves that a maximal abelian
normal subgroup H of the adjoint group is closed under subtraction.

Only that bounded step is formalized. R models NT(n,K), without an identity.
The hypotheses come respectively from the adjoint subgroup structure,
maximality (the annihilator lies in H), and Lemma 4 (H² lies in the
annihilator). Neither normality nor Lemma 4 itself is formalized here.
-/
namespace Levchuk1976

variable {R : Type*} [NonUnitalRing R]

def adjoint (a b : R) : R := a + b + a * b

theorem adjoint_subtraction_identity (a b p : R)
    (inverse : b + p + b * p = 0)
    (annihilates : adjoint a p * (b * p - a * p) = 0) :
    adjoint (adjoint a p) (b * p - a * p) = a - b := by
  unfold adjoint at *
  rw [annihilates, add_zero]
  have hp : p + b * p = -b := by
    apply eq_neg_of_add_eq_zero_right
    simpa only [add_assoc] using inverse
  calc
    a + p + a * p + (b * p - a * p) = a + (p + b * p) := by
      noncomm_ring
    _ = a - b := by rw [hp, sub_eq_add_neg]

theorem adjoint_subgroup_sub_closed (H : Set R)
    (circle_closed : ∀ a ∈ H, ∀ b ∈ H, adjoint a b ∈ H)
    (inverse_mem : ∀ b ∈ H, ∃ p ∈ H, b + p + b * p = 0)
    (annihilator_mem : ∀ c : R,
      (∀ r : R, r * c = 0 ∧ c * r = 0) → c ∈ H)
    (products_annihilate : ∀ a ∈ H, ∀ b ∈ H,
      ∀ r : R, r * (a * b) = 0 ∧ (a * b) * r = 0)
    (a b : R) (ha : a ∈ H) (hb : b ∈ H) : a - b ∈ H := by
  obtain ⟨p, hp, hinverse⟩ := inverse_mem b hb
  have hcann : ∀ r : R,
      r * (b * p - a * p) = 0 ∧ (b * p - a * p) * r = 0 := by
    intro r
    obtain ⟨hbl, hbr⟩ := products_annihilate b hb p hp r
    obtain ⟨hal, har⟩ := products_annihilate a ha p hp r
    constructor
    · simp only [mul_sub, hbl, hal, sub_self]
    · simp only [sub_mul, hbr, har, sub_self]
  have hc : b * p - a * p ∈ H := annihilator_mem _ hcann
  have hzero := (hcann (adjoint a p)).1
  rw [← adjoint_subtraction_identity a b p hinverse hzero]
  exact circle_closed _ (circle_closed a ha p hp) _ hc

end Levchuk1976

#print axioms Levchuk1976.adjoint_subtraction_identity
#print axioms Levchuk1976.adjoint_subgroup_sub_closed
