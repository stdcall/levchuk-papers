import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/- Levchuk1983, printed pp.74–75, theorem3, equations (17)–(18).
Coordinates x,y,z mean coefficients of ε21,ε32,ε31.
Matrix rows are (a,b),(c,d); e is the inverse of its determinant.
This proves the explicit coordinate automorphisms, not the classification
of all automorphisms. The concrete lower-matrix bridge is proved below;
no bundled Group/Lie instance is introduced. -/
namespace LevchukPapers1983.RankThree
variable {R : Type*} [CommRing R]

structure Coord (R : Type*) where
  x : R
  y : R
  z : R

omit [CommRing R] in
@[ext] theorem Coord.ext {u v : Coord R}
    (hx : u.x = v.x) (hy : u.y = v.y) (hz : u.z = v.z) : u = v := by
  cases u; cases v; simp_all

def adj (u v : Coord R) : Coord R :=
  ⟨u.x + v.x, u.y + v.y, u.z + v.z + u.y * v.x⟩
def add (u v : Coord R) : Coord R := ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩
def bracket (u v : Coord R) : Coord R := ⟨0, 0, u.y * v.x - v.y * u.x⟩
def det (a b c d : R) : R := a * d - b * c

def linear (a b c d : R) (u : Coord R) : Coord R :=
  ⟨a * u.x + c * u.y, b * u.x + d * u.y, det a b c d * u.z⟩
def correction (b c : R) (ψ₁ ψ₂ : R → R) (x y : R) : R :=
  ψ₁ x + ψ₂ y + b * c * x * y

def transform (a b c d : R) (ψ₁ ψ₂ : R → R) (u : Coord R) : Coord R :=
  ⟨a * u.x + c * u.y, b * u.x + d * u.y,
   det a b c d * u.z + correction b c ψ₁ ψ₂ u.x u.y⟩

theorem transform_preserves_adj (a b c d : R) (ψ₁ ψ₂ : R → R)
    (h₁ : ∀ x y, ψ₁ (x + y) = ψ₁ x + ψ₁ y + a * b * x * y)
    (h₂ : ∀ x y, ψ₂ (x + y) = ψ₂ x + ψ₂ y + c * d * x * y)
    (u v : Coord R) :
    transform a b c d ψ₁ ψ₂ (adj u v) =
      adj (transform a b c d ψ₁ ψ₂ u) (transform a b c d ψ₁ ψ₂ v) := by
  apply Coord.ext <;> simp only [transform, adj, correction, det]
  · ring
  · ring
  · rw [h₁, h₂]; ring

def inverse (a b c d e : R) (ψ₁ ψ₂ : R → R) (u : Coord R) : Coord R :=
  let x := e * (d * u.x - c * u.y)
  let y := e * (-b * u.x + a * u.y)
  ⟨x, y, e * (u.z - correction b c ψ₁ ψ₂ x y)⟩

theorem inverse_left (a b c d e : R) (ψ₁ ψ₂ : R → R)
    (he : e * det a b c d = 1) (u : Coord R) :
    inverse a b c d e ψ₁ ψ₂ (transform a b c d ψ₁ ψ₂ u) = u := by
  have hx : e * (d * (a * u.x + c * u.y) - c * (b * u.x + d * u.y)) = u.x := by
    calc
      _ = (e * det a b c d) * u.x := by simp only [det]; ring
      _ = u.x := by rw [he, one_mul]
  have hy : e * (-b * (a * u.x + c * u.y) + a * (b * u.x + d * u.y)) = u.y := by
    calc
      _ = (e * det a b c d) * u.y := by simp only [det]; ring
      _ = u.y := by rw [he, one_mul]
  apply Coord.ext
  · exact hx
  · exact hy
  · change e * (det a b c d * u.z + correction b c ψ₁ ψ₂ u.x u.y -
        correction b c ψ₁ ψ₂ _ _) = u.z
    simp only [transform]
    rw [hx, hy, add_sub_cancel_right, ← mul_assoc, he, one_mul]

theorem inverse_right (a b c d e : R) (ψ₁ ψ₂ : R → R)
    (he : e * det a b c d = 1) (u : Coord R) :
    transform a b c d ψ₁ ψ₂ (inverse a b c d e ψ₁ ψ₂ u) = u := by
  apply Coord.ext
  · change a * (e * (d * u.x - c * u.y)) + c * (e * (-b * u.x + a * u.y)) = u.x
    calc
      _ = (e * det a b c d) * u.x := by simp only [det]; ring
      _ = u.x := by rw [he, one_mul]
  · change b * (e * (d * u.x - c * u.y)) + d * (e * (-b * u.x + a * u.y)) = u.y
    calc
      _ = (e * det a b c d) * u.y := by simp only [det]; ring
      _ = u.y := by rw [he, one_mul]
  · change det a b c d * (e * (u.z - correction b c ψ₁ ψ₂ _ _)) +
        correction b c ψ₁ ψ₂ _ _ = u.z
    simp only [inverse]
    rw [← mul_assoc, mul_comm (det a b c d) e, he, one_mul, sub_add_cancel]

theorem transform_bijective (a b c d e : R) (ψ₁ ψ₂ : R → R)
    (he : e * det a b c d = 1) : Function.Bijective (transform a b c d ψ₁ ψ₂) := by
  constructor
  · intro u v h
    have := congrArg (inverse a b c d e ψ₁ ψ₂) h
    simpa only [inverse_left a b c d e ψ₁ ψ₂ he] using this
  · intro u
    exact ⟨inverse a b c d e ψ₁ ψ₂ u, inverse_right a b c d e ψ₁ ψ₂ he u⟩

theorem linear_preserves_add (a b c d : R) (u v : Coord R) :
    linear a b c d (add u v) = add (linear a b c d u) (linear a b c d v) := by
  apply Coord.ext <;> simp only [linear, add, det] <;> ring

theorem linear_preserves_bracket (a b c d : R) (u v : Coord R) :
    linear a b c d (bracket u v) = bracket (linear a b c d u) (linear a b c d v) := by
  apply Coord.ext <;> simp only [linear, bracket, det] <;> ring

theorem linear_bijective (a b c d e : R) (he : e * det a b c d = 1) :
    Function.Bijective (linear a b c d) := by
  -- Directly invert the linear map using the adjugate on the first two coordinates.
  let inv : Coord R → Coord R := fun u =>
    ⟨e * (d * u.x - c * u.y), e * (-b * u.x + a * u.y), e * u.z⟩
  have hl : ∀ u, inv (linear a b c d u) = u := by
    intro u
    apply Coord.ext
    · change e * (d * (a * u.x + c * u.y) - c * (b * u.x + d * u.y)) = u.x
      calc
        _ = (e * det a b c d) * u.x := by simp only [det]; ring
        _ = u.x := by rw [he, one_mul]
    · change e * (-b * (a * u.x + c * u.y) + a * (b * u.x + d * u.y)) = u.y
      calc
        _ = (e * det a b c d) * u.y := by simp only [det]; ring
        _ = u.y := by rw [he, one_mul]
    · change e * (det a b c d * u.z) = u.z
      rw [← mul_assoc, he, one_mul]
  have hr : ∀ u, linear a b c d (inv u) = u := by
    intro u
    apply Coord.ext
    · change a * (e * (d * u.x - c * u.y)) + c * (e * (-b * u.x + a * u.y)) = u.x
      calc
        _ = (e * det a b c d) * u.x := by simp only [det]; ring
        _ = u.x := by rw [he, one_mul]
    · change b * (e * (d * u.x - c * u.y)) + d * (e * (-b * u.x + a * u.y)) = u.y
      calc
        _ = (e * det a b c d) * u.y := by simp only [det]; ring
        _ = u.y := by rw [he, one_mul]
    · change det a b c d * (e * u.z) = u.z
      rw [← mul_assoc, mul_comm (det a b c d) e, he, one_mul]
  exact ⟨fun u v h => by simpa only [hl] using congrArg inv h, fun u => ⟨inv u, hr u⟩⟩

def zero : Coord R := ⟨0, 0, 0⟩
def groupInverse (u : Coord R) : Coord R := ⟨-u.x, -u.y, -u.z + u.y * u.x⟩

theorem adj_associative (u v w : Coord R) : adj (adj u v) w = adj u (adj v w) := by
  apply Coord.ext <;> simp only [adj] <;> ring

theorem adj_zero (u : Coord R) : adj u zero = u ∧ adj zero u = u := by
  constructor <;> apply Coord.ext <;> simp [adj, zero]

theorem adj_inverse (u : Coord R) :
    adj u (groupInverse u) = zero ∧ adj (groupInverse u) u = zero := by
  constructor <;> apply Coord.ext <;> simp only [adj, groupInverse, zero] <;> ring

-- The paper uses u⁻¹ v⁻¹ u v, with the lower-triangular orientation.
theorem commutator_eq_bracket (u v : Coord R) :
    adj (adj (adj (groupInverse u) (groupInverse v)) u) v = bracket u v := by
  apply Coord.ext <;> simp only [adj, groupInverse, bracket] <;> ring

theorem cocycle_zero (k : R) (ψ : R → R)
    (h : ∀ x y, ψ (x + y) = ψ x + ψ y + k * x * y) : ψ 0 = 0 := by
  have hh := h 0 0
  simp only [mul_zero, add_zero] at hh
  have hh' : ψ 0 + 0 = ψ 0 + ψ 0 := by simpa only [add_zero] using hh
  exact (add_left_cancel hh').symm

theorem transform_elementary (a b c d : R) (ψ₁ ψ₂ : R → R)
    (h₁ : ∀ x y, ψ₁ (x + y) = ψ₁ x + ψ₁ y + a * b * x * y)
    (h₂ : ∀ x y, ψ₂ (x + y) = ψ₂ x + ψ₂ y + c * d * x * y)
    (t : R) :
    transform a b c d ψ₁ ψ₂ ⟨t, 0, 0⟩ = ⟨a * t, b * t, ψ₁ t⟩ ∧
    transform a b c d ψ₁ ψ₂ ⟨0, t, 0⟩ = ⟨c * t, d * t, ψ₂ t⟩ ∧
    transform a b c d ψ₁ ψ₂ ⟨0, 0, t⟩ = ⟨0, 0, det a b c d * t⟩ := by
  have hz₁ := cocycle_zero (a * b) ψ₁ h₁
  have hz₂ := cocycle_zero (c * d) ψ₂ h₂
  constructor
  · apply Coord.ext <;> simp [transform, correction, hz₂]
  constructor
  · apply Coord.ext <;> simp [transform, correction, hz₁]
  · apply Coord.ext <;> simp [transform, correction, hz₁, hz₂]

theorem adjoint_coordinate_automorphism (a b c d e : R) (ψ₁ ψ₂ : R → R)
    (he : e * det a b c d = 1)
    (h₁ : ∀ x y, ψ₁ (x + y) = ψ₁ x + ψ₁ y + a * b * x * y)
    (h₂ : ∀ x y, ψ₂ (x + y) = ψ₂ x + ψ₂ y + c * d * x * y) :
    Function.Bijective (transform a b c d ψ₁ ψ₂) ∧
      ∀ u v, transform a b c d ψ₁ ψ₂ (adj u v) =
        adj (transform a b c d ψ₁ ψ₂ u) (transform a b c d ψ₁ ψ₂ v) := by
  exact ⟨transform_bijective a b c d e ψ₁ ψ₂ he,
    transform_preserves_adj a b c d ψ₁ ψ₂ h₁ h₂⟩

theorem lie_coordinate_automorphism (a b c d e : R)
    (he : e * det a b c d = 1) :
    Function.Bijective (linear a b c d) ∧
      (∀ u v, linear a b c d (add u v) = add (linear a b c d u) (linear a b c d v)) ∧
      ∀ u v, linear a b c d (bracket u v) =
        bracket (linear a b c d u) (linear a b c d v) := by
  exact ⟨linear_bijective a b c d e he,
    linear_preserves_add a b c d, linear_preserves_bracket a b c d⟩

-- Native strictly lower triangular 3×3 realization, rows/columns numbered 0,1,2.
def matrix (u : Coord R) : Matrix (Fin 3) (Fin 3) R := fun i j =>
  if i = 1 ∧ j = 0 then u.x else
  if i = 2 ∧ j = 1 then u.y else
  if i = 2 ∧ j = 0 then u.z else 0

theorem matrix_injective : Function.Injective (matrix (R := R)) := by
  intro u v h
  apply Coord.ext
  · simpa [matrix] using congrArg (fun m : Matrix (Fin 3) (Fin 3) R => m 1 0) h
  · simpa [matrix] using congrArg (fun m : Matrix (Fin 3) (Fin 3) R => m 2 1) h
  · simpa [matrix] using congrArg (fun m : Matrix (Fin 3) (Fin 3) R => m 2 0) h

theorem matrix_adj (u v : Coord R) :
    matrix (adj u v) = matrix u + matrix v + matrix u * matrix v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, adj, Matrix.mul_apply, Fin.sum_univ_succ]

theorem matrix_bracket (u v : Coord R) :
    matrix (bracket u v) = matrix u * matrix v - matrix v * matrix u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, bracket, Matrix.mul_apply, Fin.sum_univ_succ]

#print axioms matrix_injective
#print axioms matrix_adj
#print axioms matrix_bracket

#print axioms adjoint_coordinate_automorphism
#print axioms lie_coordinate_automorphism

#print axioms adj_associative
#print axioms adj_zero
#print axioms adj_inverse
#print axioms commutator_eq_bracket
#print axioms cocycle_zero
#print axioms transform_elementary

#print axioms transform_preserves_adj
#print axioms inverse_left
#print axioms inverse_right
#print axioms transform_bijective
#print axioms linear_preserves_add
#print axioms linear_preserves_bracket
#print axioms linear_bijective
end LevchukPapers1983.RankThree
