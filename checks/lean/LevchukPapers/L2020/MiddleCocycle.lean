import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin

namespace LevchukPapers.L2020.MiddleCocycle

-- Coordinates (21,31,32,41,42,43) of the strictly lower4x4 matrix.
abbrev NT4 (K : Type*) := Fin 6 → K

def product {K : Type*} [CommRing K] (x y : NT4 K) : NT4 K :=
  ![0, x 2 * y 0, 0, x 4 * y 0 + x 5 * y 1, x 5 * y 2, 0]

def deformed {K : Type*} [CommRing K] (x y : NT4 K) : NT4 K :=
  ![0, x 2 * y 0, 0, x 4 * y 0 + x 5 * y 1 + x 2 * y 2,
    x 5 * y 2, 0]

def matrix {K : Type*} [CommRing K] (x : NT4 K) : Matrix (Fin 4) (Fin 4) K :=
  ![![0, 0, 0, 0], ![x 0, 0, 0, 0], ![x 1, x 2, 0, 0],
    ![x 3, x 4, x 5, 0]]

theorem matrix_injective {K : Type*} [CommRing K] :
    Function.Injective (matrix (K := K)) := by
  intro x y h
  funext i
  fin_cases i
  · exact congrArg (fun m => m 1 0) h
  · exact congrArg (fun m => m 2 0) h
  · exact congrArg (fun m => m 2 1) h
  · exact congrArg (fun m => m 3 0) h
  · exact congrArg (fun m => m 3 1) h
  · exact congrArg (fun m => m 3 2) h

theorem matrix_product {K : Type*} [CommRing K] (x y : NT4 K) :
    matrix (product x y) = matrix x * matrix y := by
  ext i j
  change matrix (product x y) i j = ∑ k : Fin 4, matrix x i k * matrix y k j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, product, Fin.sum_univ_succ]

theorem deformed_bilinear {K : Type*} [CommRing K]
    (a : K) (x y z : NT4 K) :
    deformed (x + y) z = deformed x z + deformed y z ∧
    deformed x (y + z) = deformed x y + deformed x z ∧
    deformed (a • x) y = a • deformed x y ∧
    deformed x (a • y) = a • deformed x y := by
  constructor
  · funext i; fin_cases i <;> simp [deformed]; all_goals ring
  constructor
  · funext i; fin_cases i <;> simp [deformed]; all_goals ring
  constructor
  · funext i; fin_cases i <;> simp [deformed]; all_goals ring
  · funext i; fin_cases i <;> simp [deformed]; all_goals ring

theorem deformed_associative {K : Type*} [CommRing K] (x y z : NT4 K) :
    deformed (deformed x y) z = deformed x (deformed y z) := by
  funext i
  fin_cases i <;> simp [deformed]
  all_goals ring

theorem same_commutator {K : Type*} [CommRing K] (x y : NT4 K) :
    deformed x y - deformed y x = product x y - product y x := by
  funext i
  fin_cases i <;> simp [deformed, product]
  all_goals ring

abbrev V := NT4 (ZMod 2)
def ordinarySquareZero (x : V) : Prop := product x x = 0
def deformedSquareZero (x : V) : Prop := deformed x x = 0

instance (x : V) : Decidable (ordinarySquareZero x) := inferInstanceAs
  (Decidable (product x x = 0))
instance (x : V) : Decidable (deformedSquareZero x) := inferInstanceAs
  (Decidable (deformed x x = 0))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem ordinary_square_zero_count :
    Fintype.card {x : V // ordinarySquareZero x} = 28 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem deformed_square_zero_count :
    Fintype.card {x : V // deformedSquareZero x} = 20 := by decide

theorem not_additively_multiplicatively_isomorphic :
    ¬ ∃ f : V ≃+ V, ∀ x y : V, f (product x y) = deformed (f x) (f y) := by
  rintro ⟨f, hf⟩
  have hp (x : V) : ordinarySquareZero x ↔ deformedSquareZero (f x) := by
    unfold ordinarySquareZero deformedSquareZero
    rw [← hf]
    constructor
    · intro h
      rw [h, f.map_zero]
    · intro h
      apply f.injective
      simpa using h
  let e : {x : V // ordinarySquareZero x} ≃ {x : V // deformedSquareZero x} := {
    toFun := fun x => ⟨f x, (hp x).mp x.property⟩
    invFun := fun y => ⟨f.symm y, (hp (f.symm y)).mpr (by simpa using y.property)⟩
    left_inv := by intro x; apply Subtype.ext; exact f.symm_apply_apply x
    right_inv := by intro y; apply Subtype.ext; exact f.apply_symm_apply y
  }
  have hc := Fintype.card_congr e
  rw [ordinary_square_zero_count, deformed_square_zero_count] at hc
  contradiction

theorem not_oppositely_isomorphic :
    ¬ ∃ f : V ≃+ V, ∀ x y : V, f (product y x) = deformed (f x) (f y) := by
  rintro ⟨f, hf⟩
  have hp (x : V) : ordinarySquareZero x ↔ deformedSquareZero (f x) := by
    unfold ordinarySquareZero deformedSquareZero
    rw [← hf]
    constructor
    · intro h; rw [h, f.map_zero]
    · intro h; apply f.injective; simpa using h
  let e : {x : V // ordinarySquareZero x} ≃ {x : V // deformedSquareZero x} := {
    toFun := fun x => ⟨f x, (hp x).mp x.property⟩
    invFun := fun y => ⟨f.symm y, (hp (f.symm y)).mpr (by simpa using y.property)⟩
    left_inv := by intro x; apply Subtype.ext; exact f.symm_apply_apply x
    right_inv := by intro y; apply Subtype.ext; exact f.apply_symm_apply y
  }
  have hc := Fintype.card_congr e
  rw [ordinary_square_zero_count, deformed_square_zero_count] at hc
  contradiction

#print axioms deformed_associative
#print axioms same_commutator
#print axioms ordinary_square_zero_count
#print axioms deformed_square_zero_count
#print axioms not_additively_multiplicatively_isomorphic
#print axioms not_oppositely_isomorphic
#print axioms deformed_bilinear
#print axioms matrix_injective
#print axioms matrix_product
end LevchukPapers.L2020.MiddleCocycle
