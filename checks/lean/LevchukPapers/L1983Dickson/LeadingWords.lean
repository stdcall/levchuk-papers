import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Tactic.FinCases

/- Proposition1, pp.432–433: arbitrary-length leading coefficient
argument, with the corrected LEFT-column semigroup. Polynomials have
matrix coefficients; X is central. Every block is exactly U(k)L(lX).
The entry polynomial transports the nonzero lower-left coefficient to
the scalar transcendence argument. No finite-length bound is assumed. -/
namespace LevchukPapers.L1983Dickson
open Polynomial

def col {F : Type*} [Field F] (a b : F) : Matrix (Fin 2) (Fin 2) F :=
  fun i j => if j=0 then if i=0 then a else b else 0

def upper {F : Type*} [Field F] (k : F) : Matrix (Fin 2) (Fin 2) F :=
  fun i j => if i=j then 1 else if i=0 ∧ j=1 then k else 0

theorem col_mul {F : Type*} [Field F] (a b c d : F) :
    col a b * col c d = col (a*c) (b*c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [col,Matrix.mul_apply,Fin.sum_univ_succ]

theorem col_ne_zero {F : Type*} [Field F] {a b : F} (ha : a ≠ 0) :
    col a b ≠ 0 := by
  intro h
  have hh := congrFun (congrFun h 0) 0
  exact ha (by simpa [col] using hh)

noncomputable def block {F : Type*} [Field F] (k l : F) :
    Polynomial (Matrix (Fin 2) (Fin 2) F) :=
  C (col (k*l) l) * X + C (upper k)

noncomputable def word {F : Type*} [Field F] : List (F × F) →
    Polynomial (Matrix (Fin 2) (Fin 2) F)
  | [] => 1
  | p::ps => block p.1 p.2 * word ps

theorem leadingCoeff_block {F : Type*} [Field F] (k l : F)
    (hk : k ≠ 0) (hl : l ≠ 0) :
    (block k l).leadingCoeff = col (k*l) l := by
  exact Polynomial.leadingCoeff_linear (col_ne_zero (mul_ne_zero hk hl))

theorem leadingCoeff_word {F : Type*} [Field F] (ps : List (F × F))
    (hne : ps ≠ []) (h : ∀ p ∈ ps, p.1 ≠ 0 ∧ p.2 ≠ 0) :
    ∃ a b : F, a ≠ 0 ∧ b ≠ 0 ∧ (word ps).leadingCoeff = col a b := by
  induction ps with
  | nil => exact (hne rfl).elim
  | cons p ps ih =>
    have hp := h p (by simp)
    have hblock := leadingCoeff_block p.1 p.2 hp.1 hp.2
    cases ps with
    | nil =>
      exact ⟨p.1*p.2,p.2,mul_ne_zero hp.1 hp.2,hp.2,
        by simpa [word] using hblock⟩
    | cons q qs =>
      obtain ⟨a,b,ha,hb,hw⟩ := ih (by simp) (by
        intro r hr
        exact h r (List.mem_cons_of_mem p hr))
      have hmul : (block p.1 p.2).leadingCoeff * (word (q::qs)).leadingCoeff ≠ 0 := by
        rw [hblock,hw,col_mul]
        exact col_ne_zero (mul_ne_zero (mul_ne_zero hp.1 hp.2) ha)
      refine ⟨p.1*p.2*a,p.2*a,mul_ne_zero (mul_ne_zero hp.1 hp.2) ha,
        mul_ne_zero hp.2 ha,?_⟩
      rw [word,Polynomial.leadingCoeff_mul' hmul,hblock,hw,col_mul]

theorem leading_lower_left_ne_zero {F : Type*} [Field F]
    (ps : List (F × F)) (hne : ps ≠ [])
    (h : ∀ p ∈ ps, p.1 ≠ 0 ∧ p.2 ≠ 0) :
    (word ps).leadingCoeff 1 0 ≠ 0 := by
  obtain ⟨a,b,_,hb,hw⟩ := leadingCoeff_word ps hne h
  simpa [hw,col] using hb

noncomputable def entryPoly {F : Type*} [Field F]
    (p : Polynomial (Matrix (Fin 2) (Fin 2) F)) (i j : Fin 2) : Polynomial F :=
  ∑ n ∈ p.support, monomial n ((p.coeff n) i j)

theorem entryPoly_coeff {F : Type*} [Field F]
    (p : Polynomial (Matrix (Fin 2) (Fin 2) F)) (i j : Fin 2) (n : ℕ) :
    (entryPoly p i j).coeff n = (p.coeff n) i j := by
  classical
  simp only [entryPoly,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial]
  by_cases hn : n ∈ p.support
  · simp [hn]
  · have hp : p.coeff n=0 := by
      by_contra hnp
      exact hn (Polynomial.mem_support_iff.mpr hnp)
    simp [hn,hp]

theorem word_lower_left_polynomial_ne_zero {F : Type*} [Field F]
    (ps : List (F × F)) (hne : ps ≠ [])
    (h : ∀ p ∈ ps, p.1 ≠ 0 ∧ p.2 ≠ 0) : entryPoly (word ps) 1 0 ≠ 0 := by
  intro hz
  have hc := congrArg (fun p : Polynomial F => p.coeff (word ps).natDegree) hz
  rw [entryPoly_coeff] at hc
  apply leading_lower_left_ne_zero ps hne h
  change ((word ps).coeff (word ps).natDegree) 1 0=0
  simpa only [Polynomial.coeff_zero] using hc

theorem transcendental_word_lower_left {F K : Type*} [Field F] [Field K]
    [Algebra F K] (x : K) (hx : Transcendental F x)
    (ps : List (F × F)) (hne : ps ≠ [])
    (h : ∀ p ∈ ps, p.1 ≠ 0 ∧ p.2 ≠ 0) :
    aeval x (entryPoly (word ps) 1 0) ≠ 0 := by
  intro hzero
  exact word_lower_left_polynomial_ne_zero ps hne h
    ((transcendental_iff.mp hx) _ hzero)

end LevchukPapers.L1983Dickson

#print axioms LevchukPapers.L1983Dickson.col_mul
#print axioms LevchukPapers.L1983Dickson.col_ne_zero
#print axioms LevchukPapers.L1983Dickson.leadingCoeff_block
#print axioms LevchukPapers.L1983Dickson.leadingCoeff_word
#print axioms LevchukPapers.L1983Dickson.leading_lower_left_ne_zero
#print axioms LevchukPapers.L1983Dickson.entryPoly_coeff
#print axioms LevchukPapers.L1983Dickson.word_lower_left_polynomial_ne_zero
#print axioms LevchukPapers.L1983Dickson.transcendental_word_lower_left
