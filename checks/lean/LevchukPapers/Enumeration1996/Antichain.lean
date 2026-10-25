import Mathlib.Order.Basic
import Mathlib.Tactic.Ring

namespace LevchukPapers.Enumeration1996

/-- The root-poset step behind Lemma 1: an antichain is determined by
its upward closure. No finiteness or root-system hypothesis is needed.
Here `A` and `B` are predicates expressing membership in the two sets. -/
theorem antichain_upward_injective {P : Type*} [PartialOrder P]
    (A B : P → Prop)
    (hA : ∀ a, A a → ∀ b, A b → a ≤ b → a = b)
    (hB : ∀ a, B a → ∀ b, B b → a ≤ b → a = b)
    (h : ∀ x, (∃ a, A a ∧ a ≤ x) ↔ ∃ b, B b ∧ b ≤ x) :
    ∀ x, A x ↔ B x := by
  intro x
  constructor
  · intro hx
    obtain ⟨b, hb, hbx⟩ := (h x).mp ⟨x, hx, le_refl x⟩
    obtain ⟨a, ha, hab⟩ := (h b).mpr ⟨b, hb, le_refl b⟩
    have hax := hA a ha x hx (le_trans hab hbx)
    have hxb : x ≤ b := hax ▸ hab
    have hxb' : x = b := le_antisymm hxb hbx
    exact hxb' ▸ hb
  · intro hx
    obtain ⟨a, ha, hax⟩ := (h x).mpr ⟨x, hx, le_refl x⟩
    obtain ⟨b, hb, hba⟩ := (h a).mp ⟨a, ha, le_refl a⟩
    have hbx := hB b hb x hx (le_trans hba hax)
    have hxa : x ≤ a := hbx ▸ hba
    have hxa' : x = a := le_antisymm hxa hax
    exact hxa' ▸ ha

/-- Lemma 7's substitution w=x(1-x) has discriminant (1-2x)^2.
Selecting the inverse branch at zero still requires an analytic argument. -/
theorem substitution_discriminant {R : Type*} [CommRing R] (x : R) :
    1 - 4 * (x * (1-x)) = (1-2*x)^2 := by
  ring

/-- The two commutator coefficient columns (a,a²), (b,b²)
are independent for distinct nonzero parameters. This explains why
the argument surrounding (2) needs a field with more than two elements.
It does not assert the group commutator formula itself. -/
theorem commutator_coefficient_determinant {K : Type*} [Field K]
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) (hab : b ≠ a) :
    a*b^2-a^2*b ≠ 0 := by
  have heq : a*b^2-a^2*b = a*b*(b-a) := by ring
  rw [heq]
  exact mul_ne_zero (mul_ne_zero ha hb) (sub_ne_zero.mpr hab)

end LevchukPapers.Enumeration1996

#print axioms LevchukPapers.Enumeration1996.antichain_upward_injective
#print axioms LevchukPapers.Enumeration1996.substitution_discriminant
#print axioms LevchukPapers.Enumeration1996.commutator_coefficient_determinant
