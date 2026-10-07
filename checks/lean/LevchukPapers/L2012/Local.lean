import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Abel

/-!
Two bounded steps, not a formalization of the Lie-group classification.
1. Coordinates of formula (2): deriving the simple root from the pair.
2. Logical step of lemma 4.3: once a normal abelian subgroup attains the
global bound, maximizing within normal abelian subgroups is equivalent
to attaining the global bound. The existence/bound hypotheses are explicit.
-/

namespace LevchukPapers2012

theorem root_pair_coordinate {L : Type*} [AddCommGroup L] (ρ r r' p : L) :
    p = ρ - r - r' ↔ r + r' + p = ρ := by
  constructor
  · intro h
    rw [h]
    abel
  · intro h
    rw [← h]
    abel

theorem relative_maximum_iff_global {S : Type*}
    (A N : S → Prop) (size : S → Nat)
    (normal_is_abelian : ∀ y, N y → A y)
    (witness : S) (normal_witness : N witness)
    (global_bound : ∀ y, A y → size y ≤ size witness) (x : S) :
    (N x ∧ ∀ y, N y → size y ≤ size x) ↔
      (N x ∧ ∀ y, A y → size y ≤ size x) := by
  constructor
  · rintro ⟨hx, hmax⟩
    exact ⟨hx, fun y hy => Nat.le_trans (global_bound y hy) (hmax witness normal_witness)⟩
  · rintro ⟨hx, hmax⟩
    exact ⟨hx, fun y hy => hmax y (normal_is_abelian y hy)⟩

end LevchukPapers2012

#print axioms LevchukPapers2012.root_pair_coordinate
#print axioms LevchukPapers2012.relative_maximum_iff_global
