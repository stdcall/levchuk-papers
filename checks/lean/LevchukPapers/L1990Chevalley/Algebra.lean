import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring

namespace Levchuk1990Chevalley

/-- An element annihilating every quadratic deviation is killed by 2;
its multiplication also identifies squares with the original elements.
No restriction on characteristic or zero divisors is imposed. -/
theorem quadraticAnnihilator {R : Type*} [CommRing R] (d : R)
    (h : ∀ t : R, d * (t ^ 2 - t) = 0) :
    (2 : R) * d = 0 ∧ ∀ t : R, d * t ^ 2 = d * t := by
  constructor
  · calc
      (2 : R) * d = d * ((-1 : R) ^ 2 - (-1)) := by ring
      _ = 0 := h (-1)
  · intro t
    calc
      d * t ^ 2 = d * (t ^ 2 - t) + d * t := by ring
      _ = d * t := by rw [h t]; simp

/-- The cubic deviation multiplied by an element killed by 3 is additive.
This is the parameter identity used in the symplectic transformations;
the preservation of the root-group relations is a separate claim. -/
theorem cubicDeviationAdditive {R : Type*} [CommRing R] (b x y : R)
    (hb : (3 : R) * b = 0) :
    b * ((x + y) ^ 3 - (x + y)) =
      b * (x ^ 3 - x) + b * (y ^ 3 - y) := by
  calc
    b * ((x + y) ^ 3 - (x + y)) =
        b * (x ^ 3 - x) + b * (y ^ 3 - y) +
          (3 * b) * (x * y * (x + y)) := by ring
    _ = b * (x ^ 3 - x) + b * (y ^ 3 - y) := by rw [hb]; simp

#print axioms quadraticAnnihilator
#print axioms cubicDeviationAdditive

end Levchuk1990Chevalley
