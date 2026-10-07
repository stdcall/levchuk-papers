import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

namespace Levchuk1990SmallAutomorphisms

/-- Upper unitriangular coordinates (a,b,c) at (12,23,13). -/
structure UT3 (K : Type*) where
  a : K
  b : K
  c : K

variable {K : Type*} [CommRing K]

def product (x y : UT3 K) : UT3 K :=
  ⟨x.a + y.a, x.b + y.b, x.c + y.c + x.a * y.b⟩

def identity : UT3 K := ⟨0, 0, 0⟩
def inverse (x : UT3 K) : UT3 K := ⟨-x.a, -x.b, x.a * x.b - x.c⟩

theorem group_laws (x y z : UT3 K) :
    product (product x y) z = product x (product y z) ∧
    product identity x = x ∧ product x identity = x ∧
    product (inverse x) x = identity ∧ product x (inverse x) = identity := by
  cases x; cases y; cases z
  constructor
  · simp only [product]
    congr 1 <;> ring
  · simp [product, identity, inverse]

/-- A2 graph involution; rho(A2)=1, so the f component is unchanged. -/
def mixed (f : K) (x : UT3 K) : UT3 K :=
  ⟨f * x.a + (1 - f) * x.b,
   f * x.b + (1 - f) * x.a,
   f * x.c + (1 - f) * (x.a * x.b - x.c)⟩

theorem mixed_product (f : K) (hf : f * f = f) (x y : UT3 K) :
    mixed f (product x y) = product (mixed f x) (mixed f y) := by
  cases x; cases y
  simp only [mixed, product]
  congr 1
  · ring
  · ring
  · have hp : f ^ 2 = f := by simpa [pow_two] using hf
    ring_nf
    simp only [hp]
    ring

theorem mixed_involutive (f : K) (hf : f * f = f) (x : UT3 K) :
    mixed f (mixed f x) = x := by
  cases x
  simp only [mixed]
  congr 1 <;> have hp : f ^ 2 = f := by simpa [pow_two] using hf
  all_goals
    have hp3 : f ^ 3 = f := by calc
      f ^ 3 = f ^ 2 * f := by ring
      _ = f := by rw [hp, hf]
    ring_nf
    simp only [hp, hp3]
    ring

instance : Mul (UT3 K) := ⟨product⟩

/-- A multiplication equivalence of the group whose laws are proved above.
Its inverse is the very same map, not an assumed inverse homomorphism. -/
def mixedAutomorphism (f : K) (hf : f * f = f) : UT3 K ≃* UT3 K where
  toFun := mixed f
  invFun := mixed f
  left_inv := mixed_involutive f hf
  right_inv := mixed_involutive f hf
  map_mul' := mixed_product f hf

def rootAlpha (t : K) : UT3 K := ⟨t, 0, 0⟩
def rootBeta (t : K) : UT3 K := ⟨0, t, 0⟩
def rootHighest (t : K) : UT3 K := ⟨0, 0, t⟩

/-- All positive roots of A2: alpha, beta, alpha+beta. The graph
involution swaps the simple roots and negates the highest-root parameter.
This is exactly x_r(ft) times graph(x_r((1-f)t)). -/
theorem all_root_images (f : K) (hf : f * f = f) (t : K) :
    mixed f (rootAlpha t) =
      product (rootAlpha (f * t)) (rootBeta ((1 - f) * t)) ∧
    mixed f (rootBeta t) =
      product (rootBeta (f * t)) (rootAlpha ((1 - f) * t)) ∧
    mixed f (rootHighest t) =
      product (rootHighest (f * t)) (rootHighest (-((1 - f) * t))) := by
  have hp : f ^ 2 = f := by simpa [pow_two] using hf
  simp only [mixed, rootAlpha, rootBeta, rootHighest, product]
  constructor
  · simp only [mul_zero, add_zero, sub_zero]
    congr 1
    ring_nf
    simp only [hp]
    ring
  · constructor <;> congr 1 <;> ring

/-- The actual 3 by 3 unitriangular matrix, indexed by 0,1,2. -/
def matrix (x : UT3 K) : Matrix (Fin 3) (Fin 3) K := fun i j =>
  if i = j then 1 else
  if i = 0 ∧ j = 1 then x.a else
  if i = 1 ∧ j = 2 then x.b else
  if i = 0 ∧ j = 2 then x.c else 0

theorem matrix_product (x y : UT3 K) :
    matrix (product x y) = matrix x * matrix y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, product, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem matrix_injective : Function.Injective (matrix (K := K)) := by
  intro x y h
  have ha := congrFun (congrFun h 0) 1
  have hb := congrFun (congrFun h 1) 2
  have hc := congrFun (congrFun h 0) 2
  simp only [matrix] at ha hb hc
  simp at ha hb hc
  cases x; cases y
  cases ha; cases hb; cases hc
  rfl

#print axioms group_laws
#print axioms mixed_product
#print axioms mixed_involutive
#print axioms mixedAutomorphism
#print axioms all_root_images
#print axioms matrix_product
#print axioms matrix_injective

end Levchuk1990SmallAutomorphisms
