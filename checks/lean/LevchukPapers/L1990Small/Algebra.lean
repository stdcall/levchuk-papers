import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring

namespace Levchuk1990SmallRanks

/-- The annihilator of 6 is the sum of the annihilators of 2 and 3.
The forward decomposition is explicitly `x = 3*x + (-2*x)`.
No assumption on characteristic or zero divisors is made. -/
theorem annihilatorSixSplit {R : Type*} [CommRing R] (x : R) :
    (6 : R) * x = 0 ↔
      ∃ y z : R, (2 : R) * y = 0 ∧ (3 : R) * z = 0 ∧ x = y + z := by
  constructor
  · intro hx
    refine ⟨3 * x, -2 * x, ?_, ?_, ?_⟩
    · calc
        (2 : R) * (3 * x) = 6 * x := by ring
        _ = 0 := hx
    · calc
        (3 : R) * (-2 * x) = -(6 * x) := by ring
        _ = 0 := by rw [hx]; simp
    · ring
  · rintro ⟨y, z, hy, hz, hsplit⟩
    rw [hsplit]
    calc
      (6 : R) * (y + z) = 3 * (2 * y) + 2 * (3 * z) := by ring
      _ = 0 := by rw [hy, hz]; simp

/-- Complementary idempotents give an additive decomposition, act as
the identity on their own components, annihilate the other component,
and their principal ideals are orthogonal. -/
theorem idempotentSplit {R : Type*} [CommRing R] (f x y : R)
    (hf : f * f = f) :
    f * x + (1 - f) * x = x ∧
      f * (f * x) = f * x ∧
      (1 - f) * ((1 - f) * x) = (1 - f) * x ∧
      f * ((1 - f) * x) = 0 ∧
      (1 - f) * (f * x) = 0 ∧
      (f * x) * ((1 - f) * y) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ring
  · calc
      f * (f * x) = (f * f) * x := by ring
      _ = f * x := by rw [hf]
  · calc
      (1 - f) * ((1 - f) * x) = x - 2 * (f * x) + (f * f) * x := by ring
      _ = (1 - f) * x := by rw [hf]; ring
  · calc
      f * ((1 - f) * x) = (f - f * f) * x := by ring
      _ = 0 := by rw [hf]; ring
  · calc
      (1 - f) * (f * x) = (f - f * f) * x := by ring
      _ = 0 := by rw [hf]; ring
  · calc
      (f * x) * ((1 - f) * y) = (f - f * f) * (x * y) := by ring
      _ = 0 := by rw [hf]; ring

#print axioms annihilatorSixSplit
#print axioms idempotentSplit

end Levchuk1990SmallRanks
