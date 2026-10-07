import Mathlib.Tactic.NoncommRing

/-!
Restricted steps of `lem:l2013-thompson-cubic-trace`: the two compositions
of the cubic trace polynomial with `1 - S` vanish for an operator with
`S^3 = 1`. The statements apply in particular to the ring of linear
endomorphisms of a cubic finite-field extension. They do not formalize
rank-nullity, equality of image and kernel, or any subgroup classification.
-/
namespace LevchukPapers2013Thompson

theorem cubic_trace_annihilated_left {R : Type*} [Ring R] (S : R)
    (h : S ^ 3 = 1) : (1 - S) * (1 + S + S ^ 2) = 0 := by
  calc
    (1 - S) * (1 + S + S ^ 2) = 1 - S ^ 3 := by noncomm_ring
    _ = 0 := by rw [h]; simp

theorem cubic_trace_annihilated_right {R : Type*} [Ring R] (S : R)
    (h : S ^ 3 = 1) : (1 + S + S ^ 2) * (1 - S) = 0 := by
  calc
    (1 + S + S ^ 2) * (1 - S) = 1 - S ^ 3 := by noncomm_ring
    _ = 0 := by rw [h]; simp

end LevchukPapers2013Thompson

#print axioms LevchukPapers2013Thompson.cubic_trace_annihilated_left
#print axioms LevchukPapers2013Thompson.cubic_trace_annihilated_right
