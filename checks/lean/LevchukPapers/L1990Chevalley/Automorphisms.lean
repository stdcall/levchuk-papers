import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

namespace Levchuk1990Chevalley.C2

/-- Normal order x₂₁(x) x₁,₋₁(y) x₂,₋₁(u) x₂,₋₂(v). -/
@[ext] structure Coordinates (R : Type*) where
  x : R
  y : R
  u : R
  v : R

variable {R : Type*} [CommRing R]

instance coordMul : Mul (Coordinates R) := ⟨fun a b =>
  ⟨a.x + b.x, a.y + b.y, a.u + b.u - a.y * b.x,
    a.v + b.v + a.y * b.x ^ 2 - 2 * a.u * b.x⟩⟩
instance coordOne : One (Coordinates R) := ⟨⟨0, 0, 0, 0⟩⟩
instance coordInv : Inv (Coordinates R) := ⟨fun a =>
  ⟨-a.x, -a.y, -a.u - a.y * a.x,
    -a.v - a.y * a.x ^ 2 - 2 * a.u * a.x⟩⟩

@[simp] theorem mul_def (a b : Coordinates R) : a * b =
    ⟨a.x + b.x, a.y + b.y, a.u + b.u - a.y * b.x,
      a.v + b.v + a.y * b.x ^ 2 - 2 * a.u * b.x⟩ := rfl
@[simp] theorem one_def : (1 : Coordinates R) = ⟨0, 0, 0, 0⟩ := rfl
@[simp] theorem inv_def (a : Coordinates R) : a⁻¹ =
    ⟨-a.x, -a.y, -a.u - a.y * a.x,
      -a.v - a.y * a.x ^ 2 - 2 * a.u * a.x⟩ := rfl

instance : Group (Coordinates R) where
  mul_assoc a b c := by ext <;> simp <;> ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  inv_mul_cancel a := by ext <;> simp <;> ring

/-- The actual signed symplectic matrix in index order 1,2,-1,-2. -/
def matrix (a : Coordinates R) : Matrix (Fin 4) (Fin 4) R :=
  !![1, 0, a.y, a.u;
     a.x, 1, a.x * a.y + a.u, a.x * a.u + a.v;
     0, 0, 1, -a.x;
     0, 0, 0, 1]

theorem matrix_mul (a b : Coordinates R) : matrix (a * b) = matrix a * matrix b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem matrix_injective : Function.Injective (matrix (R := R)) := by
  intro a b h
  have hx := congrArg (fun m : Matrix (Fin 4) (Fin 4) R => m 1 0) h
  have hy := congrArg (fun m : Matrix (Fin 4) (Fin 4) R => m 0 2) h
  have hu := congrArg (fun m : Matrix (Fin 4) (Fin 4) R => m 0 3) h
  have hv := congrArg (fun m : Matrix (Fin 4) (Fin 4) R => m 1 3) h
  simp [matrix] at hx hy hu hv
  ext
  · exact hx
  · exact hy
  · exact hu
  · simpa [hx, hu] using hv

/-- Simple short root q=(2,1), simple long root r=(1,-1),
then s=(2,-1) and the highest root z=(2,-2). -/
def q (t : R) : Coordinates R := ⟨t, 0, 0, 0⟩
def r (t : R) : Coordinates R := ⟨0, t, 0, 0⟩
def s (t : R) : Coordinates R := ⟨0, 0, t, 0⟩
def z (t : R) : Coordinates R := ⟨0, 0, 0, t⟩

theorem normal_order (a : Coordinates R) :
    q a.x * r a.y * s a.u * z a.v = a := by
  ext <;> simp [q, r, s, z]

/-- The article's commutator convention A⁻¹ B⁻¹ A B,
with the negative coefficient of t²u in Lemma 3. -/
theorem short_long_commutator (t u : R) :
    (q t)⁻¹ * (r u)⁻¹ * q t * r u = s (t * u) * z (-t ^ 2 * u) := by
  ext <;> simp [q, r, s, z] <;> ring

/-- The standard alternating form in the same 1,2,-1,-2 order. -/
def form : Matrix (Fin 4) (Fin 4) R :=
  !![0, 0, 1, 0; 0, 0, 0, 1; -1, 0, 0, 0; 0, -1, 0, 0]

theorem matrix_symplectic (a : Coordinates R) :
    (matrix a).transpose * form * matrix a = form := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, form, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem matrix_one : matrix (1 : Coordinates R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix]

theorem matrix_inverse (a : Coordinates R) :
    matrix a⁻¹ * matrix a = 1 ∧ matrix a * matrix a⁻¹ = 1 := by
  constructor
  · rw [← matrix_mul, inv_mul_cancel, matrix_one]
  · rw [← matrix_mul, mul_inv_cancel, matrix_one]

/-- All normalized functional hypotheses printed after the cubic map. -/
structure CubicParameters (R : Type*) [CommRing R] where
  b : R
  lambda1 : R → R
  lambda : R → R
  lambda1_add : ∀ z t, lambda1 (z + t) = lambda1 z + lambda1 t - b * t * z
  lambda1_one : lambda1 1 = 0
  b_two : b = -lambda1 2
  lambda1_double : ∀ t, 2 * lambda1 t = b * (t - t ^ 2)
  lambda_add : ∀ z t, lambda (z + t) = lambda z + lambda t + b * t * z * (t + z - 1)

def shear (p : CubicParameters R) (a : Coordinates R) : Coordinates R :=
  ⟨a.x, a.y + p.b * a.x, a.u + p.lambda1 a.x, a.v + p.lambda a.x⟩

def unshear (p : CubicParameters R) (a : Coordinates R) : Coordinates R :=
  ⟨a.x, a.y - p.b * a.x, a.u - p.lambda1 a.x, a.v - p.lambda a.x⟩

theorem shear_mul (p : CubicParameters R) (a b : Coordinates R) :
    shear p (a * b) = shear p a * shear p b := by
  ext
  · rfl
  · simp [shear]; ring
  · simp [shear, p.lambda1_add]; ring
  · simp only [shear, mul_def]
    rw [p.lambda_add]
    have h := p.lambda1_double a.x
    linear_combination b.x * h

/-- Explicit inverse; no bijectivity assumption is made. -/
def cubicAutomorphism (p : CubicParameters R) : Coordinates R ≃* Coordinates R where
  toFun := shear p
  invFun := unshear p
  left_inv a := by ext <;> simp [shear, unshear]
  right_inv a := by ext <;> simp [shear, unshear]
  map_mul' := shear_mul p

theorem cubic_inverse_apply (p : CubicParameters R) (a : Coordinates R) :
    (cubicAutomorphism p).symm a = unshear p a := rfl

theorem lambda1_zero (p : CubicParameters R) : p.lambda1 0 = 0 := by
  have h := p.lambda1_add 0 0
  simp only [zero_add, mul_zero, sub_zero] at h
  linear_combination -h

theorem lambda_zero (p : CubicParameters R) : p.lambda 0 = 0 := by
  have h := p.lambda_add 0 0
  simp only [mul_zero, zero_mul, add_zero] at h
  linear_combination -h

/-- Exactly the displayed cubic image of q; all other roots are fixed. -/
theorem cubic_q (p : CubicParameters R) (t : R) :
    cubicAutomorphism p (q t) =
      q t * r (p.b * t) * s (p.lambda1 t) * z (p.lambda t) := by
  ext <;> simp [cubicAutomorphism, shear, q, r, s, z]

theorem cubic_other_roots (p : CubicParameters R) (t : R) :
    cubicAutomorphism p (r t) = r t ∧
    cubicAutomorphism p (s t) = s t ∧
    cubicAutomorphism p (z t) = z t := by
  constructor
  · ext <;> simp [cubicAutomorphism, shear, r, lambda1_zero, lambda_zero]
  · constructor
    · ext <;> simp [cubicAutomorphism, shear, s, lambda1_zero, lambda_zero]
    · ext <;> simp [cubicAutomorphism, shear, z, lambda1_zero, lambda_zero]

theorem cubic_commutator (p : CubicParameters R) (a b : Coordinates R) :
    cubicAutomorphism p (a⁻¹ * b⁻¹ * a * b) =
      (cubicAutomorphism p a)⁻¹ * (cubicAutomorphism p b)⁻¹ *
        cubicAutomorphism p a * cubicAutomorphism p b := by
  simp only [map_mul, map_inv]

#print axioms normal_order
#print axioms cubic_inverse_apply
#print axioms matrix_inverse
#print axioms cubic_commutator
#print axioms matrix_symplectic
#print axioms short_long_commutator
#print axioms cubic_q
#print axioms cubic_other_roots
#print axioms matrix_mul
#print axioms matrix_injective
#print axioms shear_mul
#print axioms cubicAutomorphism

end Levchuk1990Chevalley.C2
