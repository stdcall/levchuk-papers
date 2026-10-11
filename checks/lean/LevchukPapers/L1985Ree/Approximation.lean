import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Hom.Defs

/-! The transitivity step preceding Lemma 9.

`G` is the group to approximate; `H i` are intermediate groups; `K i j`
are final groups. Separation expresses that the intersection of kernels
is trivial. This theorem does not establish surjectivity, or construct
any Ree homomorphism, or prove Theorem 3.
Passage: pass:l1985-ree-transitivity.
-/

namespace LevchukPapers.L1985Ree

theorem separating_composition
    {G : Type*} [Group G] {I : Type*} {H : I → Type*}
    [∀ i, Group (H i)] {J : I → Type*} {K : (i : I) → J i → Type*}
    [∀ i j, Group (K i j)]
    (f : (i : I) → G →* H i)
    (g : (i : I) → (j : J i) → H i →* K i j)
    (hf : ∀ a : G, a ≠ 1 → ∃ i, f i a ≠ 1)
    (hg : ∀ i (b : H i), b ≠ 1 → ∃ j, g i j b ≠ 1) :
    ∀ a : G, a ≠ 1 → ∃ i j, (g i j).comp (f i) a ≠ 1 := by
  intro a ha
  obtain ⟨i, hi⟩ := hf a ha
  obtain ⟨j, hj⟩ := hg i (f i a) hi
  exact ⟨i, j, hj⟩

#print axioms separating_composition

end LevchukPapers.L1985Ree
