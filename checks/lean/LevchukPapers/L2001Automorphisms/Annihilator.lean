import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Abel

namespace Levchuk2001Automorphisms

/-- Actual NT3 coordinates: a=e21, b=e32, c=e31. -/
structure Coordinates (K : Type*) where
  a : K
  b : K
  c : K

variable {K : Type*} [Ring K]

def add (p q : Coordinates K) : Coordinates K :=
  ⟨p.a+q.a,p.b+q.b,p.c+q.c⟩

def mul (p q : Coordinates K) : Coordinates K := ⟨0,0,p.b*q.a⟩

def adjoint (p q : Coordinates K) : Coordinates K :=
  ⟨p.a+q.a,p.b+q.b,p.c+q.c+p.b*q.a⟩

def bracket (p q : Coordinates K) : Coordinates K :=
  ⟨0,0,p.b*q.a-q.b*p.a⟩

def transform (γ δ : K →+ K) (p : Coordinates K) : Coordinates K :=
  ⟨p.a,p.b,p.c+γ p.a+δ p.b⟩

def inverse (γ δ : K →+ K) (p : Coordinates K) : Coordinates K :=
  ⟨p.a,p.b,p.c-γ p.a-δ p.b⟩

theorem preserves_add (γ δ : K →+ K) (p q : Coordinates K) :
    transform γ δ (add p q)=add (transform γ δ p) (transform γ δ q) := by
  simp only [transform,add,map_add]
  congr 1
  abel

theorem preserves_mul (γ δ : K →+ K) (p q : Coordinates K) :
    transform γ δ (mul p q)=mul (transform γ δ p) (transform γ δ q) := by
  simp [transform,mul]

theorem preserves_adjoint (γ δ : K →+ K) (p q : Coordinates K) :
    transform γ δ (adjoint p q)=adjoint (transform γ δ p) (transform γ δ q) := by
  simp only [transform,adjoint,map_add]
  congr 1
  abel

theorem preserves_bracket (γ δ : K →+ K) (p q : Coordinates K) :
    transform γ δ (bracket p q)=bracket (transform γ δ p) (transform γ δ q) := by
  simp [transform,bracket]

theorem left_inverse (γ δ : K →+ K) (p : Coordinates K) :
    inverse γ δ (transform γ δ p)=p := by
  cases p
  simp only [inverse,transform]
  congr 1
  abel

theorem right_inverse (γ δ : K →+ K) (p : Coordinates K) :
    transform γ δ (inverse γ δ p)=p := by
  cases p
  simp only [inverse,transform]
  congr 1
  abel

def automorphism (γ δ : K →+ K) : Coordinates K ≃ Coordinates K where
  toFun := transform γ δ
  invFun := inverse γ δ
  left_inv := left_inverse γ δ
  right_inv := right_inverse γ δ

def matrix (p : Coordinates K) : Matrix (Fin 3) (Fin 3) K := fun i j =>
  if i=1 ∧ j=0 then p.a else
  if i=2 ∧ j=1 then p.b else
  if i=2 ∧ j=0 then p.c else 0

theorem matrix_mul (p q : Coordinates K) :
    matrix (mul p q)=matrix p * matrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix,mul,Matrix.mul_apply,Fin.sum_univ_succ]

theorem matrix_add (p q : Coordinates K) :
    matrix (add p q)=matrix p+matrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix,add]

theorem matrix_injective : Function.Injective (matrix (K:=K)) := by
  intro p q h
  have ha := congrFun (congrFun h 1) 0
  have hb := congrFun (congrFun h 2) 1
  have hc := congrFun (congrFun h 2) 0
  simp [matrix] at ha hb hc
  cases p; cases q
  cases ha; cases hb; cases hc
  rfl

#print axioms preserves_add
#print axioms preserves_mul
#print axioms preserves_adjoint
#print axioms preserves_bracket
#print axioms left_inverse
#print axioms right_inverse
#print axioms automorphism
#print axioms matrix_mul
#print axioms matrix_add
#print axioms matrix_injective

end Levchuk2001Automorphisms
