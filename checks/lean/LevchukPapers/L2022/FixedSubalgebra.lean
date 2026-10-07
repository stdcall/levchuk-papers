import Mathlib.Algebra.Lie.Basic

/- sec:l2022-graph-centralizers: fixed elements of a graph automorphism
   form a Lie subalgebra. These bounded steps only use linearity and
   preservation of the Lie bracket; they do not classify fixed algebras,
   prove the low-rank exclusions, or verify the enveloping embeddings. -/
namespace LevchukPapers2022

theorem fixed_elements_closed_add
    {L : Type*} [LieRing L] (theta : L →+ L)
    {x y : L} (hx : theta x = x) (hy : theta y = y) :
    theta (x + y) = x + y := by
  rw [map_add, hx, hy]

theorem fixed_elements_closed_bracket
    {L : Type*} [LieRing L] (theta : L →+ L)
    (preserves_bracket : ∀ x y : L, theta ⁅x, y⁆ = ⁅theta x, theta y⁆)
    {x y : L} (hx : theta x = x) (hy : theta y = y) :
    theta ⁅x, y⁆ = ⁅x, y⁆ := by
  rw [preserves_bracket, hx, hy]

theorem fixed_elements_closed_scalar
    {K L : Type*} [Ring K] [LieRing L] [Module K L]
    (theta : L →+ L)
    (preserves_scalar : ∀ (c : K) (x : L), theta (c • x) = c • theta x)
    {x : L} (hx : theta x = x) (c : K) :
    theta (c • x) = c • x := by
  rw [preserves_scalar, hx]

end LevchukPapers2022

#print axioms LevchukPapers2022.fixed_elements_closed_add

#print axioms LevchukPapers2022.fixed_elements_closed_bracket

#print axioms LevchukPapers2022.fixed_elements_closed_scalar
