import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

namespace Levchuk2016Hypercentral

/-- Lemma 3, the subcase D3=A3: x=e21, y=e2,-1, z=e32,
u=e31, v=e3,-1, w=e3,-2, with the signs of Lemma 4. -/
structure Coordinates (K : Type*) where
  x : K
  y : K
  z : K
  u : K
  v : K
  w : K

variable {K : Type*} [CommRing K]

def bracket (p q : Coordinates K) : Coordinates K :=
  ⟨0, 0, 0, p.z*q.x-p.x*q.z, p.z*q.y-p.y*q.z,
    p.x*q.v-p.v*q.x+p.y*q.u-p.u*q.y⟩

structure Parameters (K : Type*) [CommRing K] where
  a : K
  b : K
  c : K
  d : K
  determinant : a*d-b*c=1
  firstRow : 2*a*b=0
  secondRow : 2*c*d=0

def transform (A : Parameters K) (p : Coordinates K) : Coordinates K :=
  ⟨A.a*p.x+A.c*p.y, A.b*p.x+A.d*p.y, p.z,
    A.a*p.u+A.c*p.v, A.b*p.u+A.d*p.v, (A.a*A.d+A.b*A.c)*p.w⟩

def inverseTransform (A : Parameters K) (p : Coordinates K) : Coordinates K :=
  ⟨A.d*p.x-A.c*p.y, -A.b*p.x+A.a*p.y, p.z,
    A.d*p.u-A.c*p.v, -A.b*p.u+A.a*p.v, (A.a*A.d+A.b*A.c)*p.w⟩

theorem central_multiplier_square (A : Parameters K) :
    (A.a*A.d+A.b*A.c)^2=1 := by
  linear_combination (A.a*A.d-A.b*A.c+1)*A.determinant +
    (2*A.c*A.d)*A.firstRow

theorem preserves_bracket (A : Parameters K) (p q : Coordinates K) :
    transform A (bracket p q)=bracket (transform A p) (transform A q) := by
  rcases p with ⟨px, py, pz, pu, pv, pw⟩
  rcases q with ⟨qx, qy, qz, qu, qv, qw⟩
  simp only [transform, bracket]
  congr 1
  · ring
  · ring
  · ring
  · ring
  · linear_combination -(px * qu - pu * qx) * A.firstRow -
      (py * qv - pv * qy) * A.secondRow

def add (p q : Coordinates K) : Coordinates K :=
  ⟨p.x+q.x, p.y+q.y, p.z+q.z, p.u+q.u, p.v+q.v, p.w+q.w⟩

def scale (t : K) (p : Coordinates K) : Coordinates K :=
  ⟨t*p.x, t*p.y, t*p.z, t*p.u, t*p.v, t*p.w⟩

theorem linearity (A : Parameters K) (p q : Coordinates K) (t : K) :
    transform A (add p q)=add (transform A p) (transform A q) ∧
    transform A (scale t p)=scale t (transform A p) := by
  constructor
  · simp only [transform, add]
    congr 1 <;> ring
  · simp only [transform, scale]
    congr 1 <;> ring

def root (i : Fin 6) (t : K) : Coordinates K :=
  ⟨if i=0 then t else 0, if i=1 then t else 0,
    if i=2 then t else 0, if i=3 then t else 0,
    if i=4 then t else 0, if i=5 then t else 0⟩

theorem all_root_images (A : Parameters K) (t : K) :
    transform A (root 0 t)=add (root 0 (A.a*t)) (root 1 (A.b*t)) ∧
    transform A (root 1 t)=add (root 0 (A.c*t)) (root 1 (A.d*t)) ∧
    transform A (root 2 t)=root 2 t ∧
    transform A (root 3 t)=add (root 3 (A.a*t)) (root 4 (A.b*t)) ∧
    transform A (root 4 t)=add (root 3 (A.c*t)) (root 4 (A.d*t)) ∧
    transform A (root 5 t)=root 5 ((A.a*A.d+A.b*A.c)*t) := by
  simp [transform, root, add]

theorem parameter_faithful (A B : Parameters K)
    (h : transform A=transform B) : A=B := by
  have ha := congrArg Coordinates.x (congrFun h (root 0 1))
  have hb := congrArg Coordinates.y (congrFun h (root 0 1))
  have hc := congrArg Coordinates.x (congrFun h (root 1 1))
  have hd := congrArg Coordinates.y (congrFun h (root 1 1))
  simp [transform, root] at ha hb hc hd
  cases A; cases B
  cases ha; cases hb; cases hc; cases hd
  rfl

theorem left_inverse (A : Parameters K) (p : Coordinates K) :
    inverseTransform A (transform A p)=p := by
  rcases p with ⟨x, y, z, u, v, w⟩
  simp only [transform, inverseTransform]
  congr 1
  · linear_combination x * A.determinant
  · linear_combination y * A.determinant
  · linear_combination u * A.determinant
  · linear_combination v * A.determinant
  · linear_combination w * central_multiplier_square A

theorem right_inverse (A : Parameters K) (p : Coordinates K) :
    transform A (inverseTransform A p)=p := by
  rcases p with ⟨x, y, z, u, v, w⟩
  simp only [transform, inverseTransform]
  congr 1
  · linear_combination x * A.determinant
  · linear_combination y * A.determinant
  · linear_combination u * A.determinant
  · linear_combination v * A.determinant
  · linear_combination w * central_multiplier_square A

/-- A genuine bijection preserving the complete Lie multiplication. -/
def automorphism (A : Parameters K) : Coordinates K ≃ Coordinates K where
  toFun := transform A
  invFun := inverseTransform A
  left_inv := left_inverse A
  right_inv := right_inverse A

/-- Actual strictly lower triangular matrices, with v at entry 42 negated. -/
def matrix (p : Coordinates K) : Matrix (Fin 4) (Fin 4) K := fun i j =>
  if i=1 ∧ j=0 then p.x else
  if i=3 ∧ j=2 then p.y else
  if i=2 ∧ j=1 then p.z else
  if i=2 ∧ j=0 then p.u else
  if i=3 ∧ j=1 then -p.v else
  if i=3 ∧ j=0 then p.w else 0

theorem matrix_bracket (p q : Coordinates K) :
    matrix (bracket p q)=matrix p * matrix q-matrix q * matrix p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, bracket, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem matrix_injective : Function.Injective (matrix (K:=K)) := by
  intro p q h
  have hx := congrFun (congrFun h 1) 0
  have hy := congrFun (congrFun h 3) 2
  have hz := congrFun (congrFun h 2) 1
  have hu := congrFun (congrFun h 2) 0
  have hv := congrFun (congrFun h 3) 1
  have hw := congrFun (congrFun h 3) 0
  simp [matrix] at hx hy hz hu hv hw
  cases p; cases q
  cases hx; cases hy; cases hz; cases hu; cases hv; cases hw
  rfl

#print axioms central_multiplier_square
#print axioms preserves_bracket
#print axioms linearity
#print axioms all_root_images
#print axioms parameter_faithful
#print axioms left_inverse
#print axioms right_inverse
#print axioms automorphism
#print axioms matrix_bracket
#print axioms matrix_injective

end Levchuk2016Hypercentral
