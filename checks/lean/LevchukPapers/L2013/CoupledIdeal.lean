import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/- The counterexample attached to th:l2013-ideals-diagonal-invariant-description.
   These identities prove two-sided closure of the coupled square-zero ideal
   H = {ε a I₂ + ε b e₂₁}. They do not prove the enumeration theorem. -/
namespace LevchukPapers2013

variable {R : Type*} [CommRing R]

def radicalEntry (ε u v w z : R) : Matrix (Fin 2) (Fin 2) R :=
  !![ε * u, ε * v; w, ε * z]

def coupledEntry (ε a b : R) : Matrix (Fin 2) (Fin 2) R :=
  !![ε * a, 0; ε * b, ε * a]

theorem radical_mul_coupled (ε u v w z a b : R) (hε : ε ^ 2 = 0) :
    radicalEntry ε u v w z * coupledEntry ε a b =
    coupledEntry ε 0 (w * a) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [radicalEntry, coupledEntry, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;> simp [hε]

theorem coupled_mul_radical (ε u v w z a b : R) (hε : ε ^ 2 = 0) :
    coupledEntry ε a b * radicalEntry ε u v w z =
    coupledEntry ε 0 (a * w) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [radicalEntry, coupledEntry, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;> simp [hε]

theorem coupled_add (ε a b c d : R) :
    coupledEntry ε a b + coupledEntry ε c d =
    coupledEntry ε (a + c) (b + d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coupledEntry] <;> ring

#print axioms radical_mul_coupled
#print axioms coupled_mul_radical
#print axioms coupled_add

end LevchukPapers2013
