import Mathlib.Algebra.Ring.Basic

/- pass:l2019-nonfinitary-quasi-inverse-truncation: separation of the lower
   diagonal filtration, and passage from congruences to an actual inverse.
   This does not construct the infinite series or prove the classifications. -/
namespace LevchukPapers2019Nonfinitary

def lowerDiagonal {A : Type*} [Zero A] (k : Nat) (x : Nat → Nat → A) : Prop :=
  ∀ i j, i - j < k → x i j = 0

theorem lower_diagonal_separated {A : Type*} [Zero A] (x : Nat → Nat → A)
    (h : ∀ k, lowerDiagonal k x) : x = 0 := by
  funext i j
  exact h (i - j + 1) i j (Nat.lt_succ_self (i - j))

theorem quasi_inverse_from_all_congruences {A : Type*} [Ring A]
    (a g : Nat → Nat → A) (ag ga : Nat → Nat → A)
    (hLeft : ∀ k, lowerDiagonal k (fun i j => a i j + g i j + ag i j))
    (hRight : ∀ k, lowerDiagonal k (fun i j => g i j + a i j + ga i j)) :
    (fun i j => a i j + g i j + ag i j) = 0 ∧
      (fun i j => g i j + a i j + ga i j) = 0 := by
  exact ⟨lower_diagonal_separated _ hLeft, lower_diagonal_separated _ hRight⟩

end LevchukPapers2019Nonfinitary

#print axioms LevchukPapers2019Nonfinitary.lower_diagonal_separated
#print axioms LevchukPapers2019Nonfinitary.quasi_inverse_from_all_congruences
