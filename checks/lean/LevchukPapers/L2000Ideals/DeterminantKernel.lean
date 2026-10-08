import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/- Matrix identities underlying the determinant-kernel example. -/
namespace LevchukPapers.L2000Ideals

open Matrix

variable {K : Type*} [CommRing K]

def upper (a : K) : Matrix (Fin 2) (Fin 2) K := !![0, a; 0, 0]
def lower : Matrix (Fin 2) (Fin 2) K := !![0, 0; 1, 0]

theorem adjoint_matrix_hom (a b : Matrix (Fin 2) (Fin 2) K) :
    (1 + a) * (1 + b) = 1 + (a + b + a * b) := by
  simp only [add_mul, mul_add, one_mul, mul_one]
  abel

theorem upper_det (a : K) : Matrix.det (1 + upper a) = 1 := by
  simp [Matrix.det_fin_two, upper]

theorem upper_inverse (a : K) :
    (1 + upper a) * (1 - upper a) = 1 ∧
    (1 - upper a) * (1 + upper a) = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [upper, Matrix.mul_apply, Fin.sum_univ_two]

theorem commutator_matrix (a : K) :
    upper a * lower - lower * upper a = !![a, 0; 0, -a] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upper, lower]

theorem commutator_det (a : K) :
    Matrix.det (1 + (upper a * lower - lower * upper a)) = 1 - a ^ 2 := by
  rw [commutator_matrix]
  simp [Matrix.det_fin_two]
  ring

theorem commutator_outside_kernel (a : K) (ha : a ^ 2 ≠ 0) :
    Matrix.det (1 + (upper a * lower - lower * upper a)) ≠ 1 := by
  rw [commutator_det]
  intro h
  apply ha
  have : -(a ^ 2) = 0 := by
    exact add_left_cancel (show (1 : K) + -(a ^ 2) = 1 + 0 by simpa using h)
  exact neg_eq_zero.mp this

theorem determinant_kernel_conjugation
    (g h : (Matrix (Fin 2) (Fin 2) K)ˣ)
    (hh : Matrix.det (h : Matrix (Fin 2) (Fin 2) K) = 1) :
    Matrix.det ((g * h * g⁻¹ : (Matrix (Fin 2) (Fin 2) K)ˣ) :
      Matrix (Fin 2) (Fin 2) K) = 1 := by
  change Matrix.det ((g : Matrix (Fin 2) (Fin 2) K) *
    (h : Matrix (Fin 2) (Fin 2) K) * (↑(g⁻¹) : Matrix (Fin 2) (Fin 2) K)) = 1
  rw [Matrix.det_mul, Matrix.det_mul, hh, mul_one]
  rw [← Matrix.det_mul]
  simp

#print axioms adjoint_matrix_hom
#print axioms upper_det
#print axioms upper_inverse
#print axioms commutator_matrix
#print axioms commutator_det
#print axioms commutator_outside_kernel
#print axioms determinant_kernel_conjugation

end LevchukPapers.L2000Ideals
