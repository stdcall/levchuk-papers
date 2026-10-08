import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/- A bounded rank-two symplectic root calculation for printed p.239.
In one-based 4×4 indices, A=E12−E43, B=E14+E23 and C=E13.
The source root elements x e_ij and y e_ij' are represented by I+xA
and I+yB. The long root e_ii' is represented by I+tC.
The source convention [X,Y]=X⁻¹Y⁻¹XY has positive coefficient 2xy.
The coefficient ring is arbitrary commutative with identity: torsion,
zero divisors and characteristic 2 are permitted. This verifies the
root relation in this model, not any arbitrary-chain classification.
Passage: pass:l1992-chevalley-symplectic-commutators. -/
namespace LevchukPapers.L1992Chevalley

def A {R : Type*} [CommRing R] : Matrix (Fin 4) (Fin 4) R :=
  fun i j => match i.val, j.val with
    | 0, 1 => 1
    | 3, 2 => -1
    | _, _ => 0

def B {R : Type*} [CommRing R] : Matrix (Fin 4) (Fin 4) R :=
  fun i j => match i.val, j.val with
    | 0, 3 => 1
    | 1, 2 => 1
    | _, _ => 0

def C {R : Type*} [CommRing R] : Matrix (Fin 4) (Fin 4) R :=
  fun i j => match i.val, j.val with
    | 0, 2 => 1
    | _, _ => 0

def rootX {R : Type*} [CommRing R] (x : R) : Matrix (Fin 4) (Fin 4) R :=
  1 + x • A

def rootY {R : Type*} [CommRing R] (y : R) : Matrix (Fin 4) (Fin 4) R :=
  1 + y • B

def longRoot {R : Type*} [CommRing R] (t : R) : Matrix (Fin 4) (Fin 4) R :=
  1 + t • C

theorem root_basis_products {R : Type*} [CommRing R] :
    (A : Matrix (Fin 4) (Fin 4) R) * A = 0 ∧ B * B = 0 ∧
      A * B = C ∧ B * A = -C ∧ A * C = 0 ∧ C * A = 0 ∧
      B * C = 0 ∧ C * B = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, B, C, Matrix.mul_apply, Fin.sum_univ_succ]

theorem rootX_mul {R : Type*} [CommRing R] (x y : R) :
    rootX x * rootX y = rootX (x + y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootX, A, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem rootY_mul {R : Type*} [CommRing R] (x y : R) :
    rootY x * rootY y = rootY (x + y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootY, B, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem rootX_inverse {R : Type*} [CommRing R] (x : R) :
    rootX (-x) * rootX x = 1 ∧ rootX x * rootX (-x) = 1 := by
  constructor <;> simp [rootX_mul, rootX]

theorem rootY_inverse {R : Type*} [CommRing R] (y : R) :
    rootY (-y) * rootY y = 1 ∧ rootY y * rootY (-y) = 1 := by
  constructor <;> simp [rootY_mul, rootY]

theorem symplectic_commutator {R : Type*} [CommRing R] (x y : R) :
    rootX (-x) * rootY (-y) * rootX x * rootY y = longRoot (2 * x * y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootX, rootY, longRoot, A, B, C,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

end LevchukPapers.L1992Chevalley

#print axioms LevchukPapers.L1992Chevalley.root_basis_products
#print axioms LevchukPapers.L1992Chevalley.rootX_mul
#print axioms LevchukPapers.L1992Chevalley.rootY_mul
#print axioms LevchukPapers.L1992Chevalley.rootX_inverse
#print axioms LevchukPapers.L1992Chevalley.rootY_inverse
#print axioms LevchukPapers.L1992Chevalley.symplectic_commutator
