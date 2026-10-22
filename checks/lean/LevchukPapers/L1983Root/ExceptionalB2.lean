import Mathlib.Algebra.CharP.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/- The scalar elimination at the end of §3, printed p.514.
The matrix calculations in B₂ have already supplied the two equalities
a²+a⁴=a⁻² and a⁴+a⁶=a⁻². These lemmas check only their scalar consequence;
they do not assume or prove the preceding group calculations or Theorem 1.
The nonzero hypothesis is the printed condition α ∈ K*.
Passage: the final scalar elimination in §3. -/
namespace LevchukPapers.L1983Root

theorem fourth_power_one_of_equal_sums {K : Type*} [Field K]
    (a : K) (ha : a ≠ 0)
    (h : a ^ 2 + a ^ 4 = a ^ 4 + a ^ 6) : a ^ 4 = 1 := by
  have hz : a ^ 2 * (a ^ 4 - 1) = 0 := by
    linear_combination -h
  have hp : a ^ 4 - 1 = 0 := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ ha)
  exact sub_eq_zero.mp hp

theorem exceptional_B2_scalar {K : Type*} [Field K] [CharP K 2]
    (a : K) (ha : a ≠ 0)
    (h₁ : a ^ 2 + a ^ 4 = (a⁻¹) ^ 2)
    (h₂ : a ^ 4 + a ^ 6 = (a⁻¹) ^ 2) : a = 1 := by
  have h4 := fourth_power_one_of_equal_sums a ha (h₁.trans h₂.symm)
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hsq : (a ^ 2 - 1) ^ 2 = 0 := by
    linear_combination h4 + (1 - a ^ 2) * htwo
  have h2 : a ^ 2 - 1 = 0 := (mul_self_eq_zero.mp (by simpa [pow_two] using hsq))
  have hsq' : (a - 1) ^ 2 = 0 := by
    linear_combination h2 + (1 - a) * htwo
  exact sub_eq_zero.mp (mul_self_eq_zero.mp (by simpa [pow_two] using hsq'))

end LevchukPapers.L1983Root

#print axioms LevchukPapers.L1983Root.fourth_power_one_of_equal_sums
#print axioms LevchukPapers.L1983Root.exceptional_B2_scalar
