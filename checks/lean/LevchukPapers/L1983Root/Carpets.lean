import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Scalar steps in §2. NonUnitalSubalgebra models an additive subring
which is an R-module: containing 1 is a conclusion, not a hypothesis.
No root-system classification is asserted by these lemmas. -/
namespace LevchukPapers.L1983Root
open Polynomial

variable {R K : Type*} [Field R] [Field K] [Algebra R K]

theorem positive_polynomial_mem (J : NonUnitalSubalgebra R K)
    {x : K} (hx : x ∈ J) (p : R[X]) : x * aeval x p ∈ J := by
  have powers : ∀ n : ℕ, x ^ (n + 1) ∈ J := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih => simpa [pow_succ] using J.mul_mem ih hx
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa [map_add, mul_add] using J.add_mem hp hq
  | monomial n r =>
    simpa [aeval_monomial, Algebra.smul_def, mul_comm, mul_left_comm,
      mul_assoc, pow_succ] using J.smul_mem r (powers n)

theorem one_mem_of_algebraic_nonzero (J : NonUnitalSubalgebra R K)
    {x : K} (hx : x ∈ J) (hn : x ≠ 0) (ha : IsAlgebraic R x) :
    (1 : K) ∈ J := by
  let p := minpoly R x
  have hi : IsIntegral R x := ha.isIntegral
  have hc : p.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hi hn
  have hp : aeval x p = 0 := minpoly.aeval R x
  have he : x * aeval x (divX p) = -algebraMap R K (p.coeff 0) := by
    have h := congrArg (aeval x) (divX_mul_X_add p)
    simp only [map_add, map_mul, aeval_X, aeval_C] at h
    rw [hp] at h
    exact eq_neg_of_add_eq_zero_left (by simpa [mul_comm] using h)
  have hm := J.smul_mem (-(p.coeff 0)⁻¹)
    (positive_polynomial_mem J hx (divX p))
  rw [he, Algebra.smul_def] at hm
  simpa [map_neg, map_inv₀, hc] using hm

theorem inv_mem_of_algebraic_module_ring (J : NonUnitalSubalgebra R K)
    {x : K} (hx : x ∈ J) (ha : IsAlgebraic R x) : x⁻¹ ∈ J := by
  by_cases hn : x = 0
  · simp [hn]
  have h1 := one_mem_of_algebraic_nonzero J hx hn ha
  have powers : ∀ n : ℕ, x ^ n ∈ J := by
    intro n
    induction n with
    | zero => simpa using h1
    | succ n ih => simpa [pow_succ] using J.mul_mem ih hx
  have evalmem (p : R[X]) : aeval x p ∈ J := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa [map_add] using J.add_mem hp hq
    | monomial n r =>
      simpa [aeval_monomial, Algebra.smul_def] using J.smul_mem r (powers n)
  let p := minpoly R x
  have hc : p.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero ha.isIntegral hn
  have hp : aeval x p = 0 := minpoly.aeval R x
  rw [inv_eq_of_root_of_coeff_zero_ne_zero hp hc]
  have hm := J.smul_mem (-(p.coeff 0)⁻¹) (evalmem (divX p))
  simpa [Algebra.smul_def, map_neg, map_inv₀, div_eq_mul_inv, mul_comm] using hm

/- A character acts by nonzero scalar multiplication. This identity
handles arbitrary root exponents, including bad characteristic: there is
no division by a Chevalley constant. -/
theorem character_scaled_monomial (c u v a b : K) (i j : ℕ) :
    c * (a * u) ^ i * (b * v) ^ j =
      (a ^ i * b ^ j) * (c * u ^ i * v ^ j) := by ring

def ScaledMember {I : Type*} (A : I → AddSubgroup K) (chi : I → K)
    (r : I) (x : K) : Prop := ∃ u ∈ A r, x = chi r * u

theorem scaling_preserves_carpet_monomial {I : Type*}
    (A : I → AddSubgroup K) (chi : I → K) (r s t : I)
    (c : K) (i j : ℕ)
    (hchi : chi t = chi r ^ i * chi s ^ j)
    (hcarpet : ∀ u ∈ A r, ∀ v ∈ A s, c * u ^ i * v ^ j ∈ A t)
    {x y : K} (hx : ScaledMember A chi r x)
    (hy : ScaledMember A chi s y) :
    ScaledMember A chi t (c * x ^ i * y ^ j) := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  refine ⟨c * u ^ i * v ^ j, hcarpet u hu v hv, ?_⟩
  rw [hchi]
  exact character_scaled_monomial c u v (chi r) (chi s) i j

theorem normalizes_negative_basis (c : K) (hc : c ≠ 0) :
    c⁻¹ * c = (1 : K) := inv_mul_cancel₀ hc

theorem subfields_equal_of_common_scaled_inclusions (P Q : Subfield K)
    (c : K) (hc : c ≠ 0) (hp : c ∈ P) (hq : c ∈ Q)
    (hPQ : ∀ x ∈ P, c * x ∈ Q) (hQP : ∀ x ∈ Q, c * x ∈ P) :
    P = Q := by
  apply SetLike.ext
  intro x
  constructor
  · intro hx
    have h := Q.mul_mem (Q.inv_mem hq) (hPQ x hx)
    simpa [← mul_assoc, inv_mul_cancel₀ hc] using h
  · intro hx
    have h := P.mul_mem (P.inv_mem hp) (hQP x hx)
    simpa [← mul_assoc, inv_mul_cancel₀ hc] using h

end LevchukPapers.L1983Root

#print axioms LevchukPapers.L1983Root.positive_polynomial_mem
#print axioms LevchukPapers.L1983Root.one_mem_of_algebraic_nonzero
#print axioms LevchukPapers.L1983Root.inv_mem_of_algebraic_module_ring
#print axioms LevchukPapers.L1983Root.character_scaled_monomial
#print axioms LevchukPapers.L1983Root.scaling_preserves_carpet_monomial
#print axioms LevchukPapers.L1983Root.normalizes_negative_basis
#print axioms LevchukPapers.L1983Root.subfields_equal_of_common_scaled_inclusions
