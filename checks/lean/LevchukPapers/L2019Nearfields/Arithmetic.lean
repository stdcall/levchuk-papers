import Mathlib.GroupTheory.OrderOfElement

/-!
A bounded general step in the proof of Theorem 4 (the spectrum condition).
The homomorphism `f` models the projection to the cyclic quotient by <a>.
Its kernel contains `a`, and the image of `b` has order `n`.
These structural hypotheses are explicit: this file does not establish
the classification of near-fields or the presentation's order.

Passage: th:l2019-nearfields-spectrum.
-/

namespace LevchukPapers.L2019Nearfields

theorem quotient_order_divides_exponent
    {G H : Type*} [Group G] [Group H] (f : G →* H)
    (a b : G) (k s z n : ℕ) (ha : f a = 1)
    (hb : orderOf (f b) = n) (h : (a ^ k * b ^ s) ^ z = 1) :
    n ∣ s * z := by
  have image : (f b) ^ (s * z) = 1 := by
    have mapped := congrArg f h
    simpa [map_pow, map_mul, ha, pow_mul] using mapped
  rw [← hb]
  exact orderOf_dvd_of_pow_eq_one image

end LevchukPapers.L2019Nearfields

#print axioms LevchukPapers.L2019Nearfields.quotient_order_divides_exponent
