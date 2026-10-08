import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Data.ZMod.Basic

namespace LevchukPapers.L2012Model

abbrev D := TrivSqZeroExt (ZMod 2) (ZMod 2)
def zEmbed (a : ZMod 2) : ZMod 4 := 2 * (a.val : ZMod 4)
def dEmbed (a : ZMod 2) : D := TrivSqZeroExt.inr a

theorem zEmbedding : Function.Injective zEmbed ∧
    (∀ a b, zEmbed (a + b) = zEmbed a + zEmbed b) ∧
    (∀ a b, zEmbed a * zEmbed b = 0) := by decide

theorem zIdeal : ∀ r : ZMod 4, ∀ a : ZMod 2,
    ∃ b : ZMod 2, r * zEmbed a = zEmbed b := by decide

theorem zGenerated : ∀ r : ZMod 4,
    ∃ a : ZMod 2, ∃ n : Fin 2, r = zEmbed a + (n.val : ZMod 4) := by decide

theorem zIndexTwo :
    ¬ (1 : ZMod 4) ∈ Set.range zEmbed ∧ (2 : ZMod 4) ∈ Set.range zEmbed := by decide

theorem dEmbedding : Function.Injective dEmbed ∧
    (∀ a b, dEmbed (a + b) = dEmbed a + dEmbed b) ∧
    (∀ a b, dEmbed a * dEmbed b = 0) := by
  refine ⟨TrivSqZeroExt.inr_injective, ?_, ?_⟩
  · intro a b; exact TrivSqZeroExt.inr_add (ZMod 2) a b
  · intro a b; exact TrivSqZeroExt.inr_mul_inr _ a b

theorem dIdeal (r : D) (a : ZMod 2) :
    r * dEmbed a = dEmbed (r.fst * a) := by
  apply TrivSqZeroExt.ext <;> simp [dEmbed, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul]

theorem dGenerated (r : D) :
    ∃ a : ZMod 2, ∃ n : Fin 2, r = dEmbed a + (n.val : D) := by
  refine ⟨r.snd, ⟨r.fst.val, r.fst.val_lt⟩, ?_⟩
  apply TrivSqZeroExt.ext
  · change r.fst = 0 + (r.fst.val : ZMod 2)
    rw [zero_add, ZMod.natCast_zmod_val]
  · change r.snd = r.snd + 0
    rw [add_zero]

theorem dIndexTwo :
    ¬ (1 : D) ∈ Set.range dEmbed ∧ (2 : D) = 0 := by
  constructor
  · rintro ⟨a, h⟩
    have := congrArg TrivSqZeroExt.fst h
    simp [dEmbed] at this
  · change (1 + 1 : D) = 0
    apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add]
    decide

theorem notRingEquiv : ¬ Nonempty (ZMod 4 ≃+* D) := by
  rintro ⟨f⟩
  have h : f (2 : ZMod 4) = f 0 := by
    change f (1 + 1) = f 0
    rw [map_add, map_one, map_zero]
    exact dIndexTwo.2
  have h' := f.injective h
  exact (by decide : (2 : ZMod 4) ≠ 0) h'

theorem unitNotInImage {R : Type*} [Ring R] (f : ZMod 2 → R)
    (hinj : Function.Injective f) (hzero : f 0 = 0)
    (hmul : ∀ a b, f a * f b = 0) : ¬ (1 : R) ∈ Set.range f := by
  rintro ⟨a, ha⟩
  have h : f 1 = f 0 := by
    rw [hzero, ← one_mul (f 1), ← ha]
    exact hmul a 1
  exact (by decide : (1 : ZMod 2) ≠ 0) (hinj h)

end LevchukPapers.L2012Model

#print axioms LevchukPapers.L2012Model.zEmbedding
#print axioms LevchukPapers.L2012Model.zIdeal
#print axioms LevchukPapers.L2012Model.zGenerated
#print axioms LevchukPapers.L2012Model.zIndexTwo
#print axioms LevchukPapers.L2012Model.dEmbedding
#print axioms LevchukPapers.L2012Model.dIdeal
#print axioms LevchukPapers.L2012Model.dGenerated
#print axioms LevchukPapers.L2012Model.dIndexTwo
#print axioms LevchukPapers.L2012Model.notRingEquiv
#print axioms LevchukPapers.L2012Model.unitNotInImage
