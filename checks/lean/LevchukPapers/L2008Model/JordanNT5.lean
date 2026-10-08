import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace LevchukPapers.L2008Model

@[ext] structure NT5 where
  a21 : ZMod 2
  a31 : ZMod 2
  a32 : ZMod 2
  a41 : ZMod 2
  a42 : ZMod 2
  a43 : ZMod 2
  a51 : ZMod 2
  a52 : ZMod 2
  a53 : ZMod 2
  a54 : ZMod 2

def add (a b : NT5) : NT5 :=
  ⟨a.a21+b.a21,a.a31+b.a31,a.a32+b.a32,a.a41+b.a41,a.a42+b.a42,
   a.a43+b.a43,a.a51+b.a51,a.a52+b.a52,a.a53+b.a53,a.a54+b.a54⟩

def mul (a b : NT5) : NT5 :=
  ⟨0,a.a32*b.a21,0,a.a42*b.a21+a.a43*b.a31,a.a43*b.a32,0,
   a.a52*b.a21+a.a53*b.a31+a.a54*b.a41,
   a.a53*b.a32+a.a54*b.a42,a.a54*b.a43,0⟩

def jordan (a b : NT5) : NT5 := add (mul a b) (mul b a)

def toMatrix (a : NT5) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  fun i j => match i.val,j.val with
    | 1,0 => a.a21
    | 2,0 => a.a31
    | 2,1 => a.a32
    | 3,0 => a.a41
    | 3,1 => a.a42
    | 3,2 => a.a43
    | 4,0 => a.a51
    | 4,1 => a.a52
    | 4,2 => a.a53
    | 4,3 => a.a54
    | _,_ => 0

def shear (a : NT5) : NT5 :=
  ⟨a.a21,a.a31,a.a32,a.a41,a.a42,a.a43,a.a51,
   a.a52+a.a31,a.a53+a.a21,a.a54⟩

theorem matrix_add (a b : NT5) : toMatrix (add a b) = toMatrix a + toMatrix b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMatrix, add, Matrix.add_apply]

theorem matrix_mul (a b : NT5) : toMatrix (mul a b) = toMatrix a * toMatrix b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMatrix, mul, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals ring

theorem matrix_faithful : Function.Injective toMatrix := by
  intro a b h
  apply NT5.ext
  · simpa [toMatrix] using congrArg (fun m => m 1 0) h
  · simpa [toMatrix] using congrArg (fun m => m 2 0) h
  · simpa [toMatrix] using congrArg (fun m => m 2 1) h
  · simpa [toMatrix] using congrArg (fun m => m 3 0) h
  · simpa [toMatrix] using congrArg (fun m => m 3 1) h
  · simpa [toMatrix] using congrArg (fun m => m 3 2) h
  · simpa [toMatrix] using congrArg (fun m => m 4 0) h
  · simpa [toMatrix] using congrArg (fun m => m 4 1) h
  · simpa [toMatrix] using congrArg (fun m => m 4 2) h
  · simpa [toMatrix] using congrArg (fun m => m 4 3) h

theorem shear_add (a b : NT5) : shear (add a b) = add (shear a) (shear b) := by
  apply NT5.ext <;> simp [shear, add] <;> ring

theorem shear_involution (a : NT5) : shear (shear a) = a := by
  apply NT5.ext <;> simp [shear] <;> (ring_nf; all_goals simp [show (2 : ZMod 2) = 0 from by decide])

theorem shear_jordan (a b : NT5) :
    shear (jordan a b) = jordan (shear a) (shear b) := by
  apply NT5.ext <;> simp [shear, jordan, mul, add] <;> (ring_nf; all_goals simp [show (2 : ZMod 2) = 0 from by decide])

theorem shear_bijective : Function.Bijective shear := by
  constructor
  · intro a b h
    calc
      a = shear (shear a) := (shear_involution a).symm
      _ = shear (shear b) := congrArg shear h
      _ = b := shear_involution b
  · intro a
    exact ⟨shear a, shear_involution a⟩

theorem matrix_jordan (a b : NT5) :
    toMatrix (jordan a b) = toMatrix a * toMatrix b + toMatrix b * toMatrix a := by
  simp only [jordan, matrix_add, matrix_mul]

def e21 : NT5 := ⟨1,0,0,0,0,0,0,0,0,0⟩
def e32 : NT5 := ⟨0,0,1,0,0,0,0,0,0,0⟩

/-- Rectangular lower-triangular ideal: rows at least i, columns at most j. -/
def ideal (i j : Nat) (a : NT5) : Prop :=
  ∀ r s : Fin 5, (r.val < i ∨ j < s.val) → toMatrix a r s = 0

theorem shear_internal_ideals (a : NT5) :
    (ideal 2 1 (shear a) ↔ ideal 2 1 a) ∧
    (ideal 3 1 (shear a) ↔ ideal 3 1 a) ∧
    (ideal 3 2 (shear a) ↔ ideal 3 2 a) := by
  simp [ideal, Fin.forall_fin_succ, toMatrix, shear]
  constructor <;> intro h <;> simp [h]

theorem shear_not_associative : shear (mul e32 e21) ≠ mul (shear e32) (shear e21) := by
  intro h
  have bad := congrArg NT5.a52 h
  norm_num [shear,mul,e32,e21] at bad

theorem shear_does_not_preserve_boundary : ideal 1 0 e21 ∧ ¬ ideal 1 0 (shear e21) := by
  constructor
  · simp [ideal, Fin.forall_fin_succ, toMatrix, e21]
  · intro h
    have bad := h 4 2 (by decide)
    norm_num [toMatrix,shear,e21] at bad


end LevchukPapers.L2008Model

#print axioms LevchukPapers.L2008Model.matrix_add
#print axioms LevchukPapers.L2008Model.matrix_mul
#print axioms LevchukPapers.L2008Model.matrix_faithful
#print axioms LevchukPapers.L2008Model.shear_add
#print axioms LevchukPapers.L2008Model.shear_involution
#print axioms LevchukPapers.L2008Model.shear_jordan
#print axioms LevchukPapers.L2008Model.shear_bijective
#print axioms LevchukPapers.L2008Model.matrix_jordan
#print axioms LevchukPapers.L2008Model.shear_internal_ideals
#print axioms LevchukPapers.L2008Model.shear_not_associative
#print axioms LevchukPapers.L2008Model.shear_does_not_preserve_boundary
