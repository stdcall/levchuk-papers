import Mathlib.ModelTheory.Algebra.Field.IsAlgClosed
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.RingTheory.Localization.Cardinality
import Mathlib.Data.Rat.Encodable

noncomputable section
namespace LevchukPapers.L2018Malcev

abbrev A := AlgebraicClosure ℚ
abbrev B := AlgebraicClosure (RatFunc ℚ)

local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

local instance : FirstOrder.Ring.CompatibleRing A :=
  FirstOrder.Ring.compatibleRingOfRing A
local instance : FirstOrder.Ring.CompatibleRing B :=
  FirstOrder.Ring.compatibleRingOfRing B

theorem elementaryEquivalent :
    FirstOrder.Language.ElementarilyEquivalent FirstOrder.Language.ring A B := by
  exact (FirstOrder.Field.ACF_isComplete (Or.inr rfl)).models_elementarily_equivalent A B

theorem transcendentalInB :
    Transcendental ℚ (algebraMap (RatFunc ℚ) B RatFunc.X) := by
  have hc : RingHom.comp (algebraMap ℚ B) (RingEquiv.refl ℚ) =
      RingHom.comp (algebraMap (RatFunc ℚ) B) (algebraMap ℚ (RatFunc ℚ)) := by
    ext x
    simp
  exact (transcendental_ringHom_iff_of_comp_eq (RingEquiv.refl ℚ)
    (algebraMap (RatFunc ℚ) B) (algebraMap (RatFunc ℚ) B).injective hc).2
    RatFunc.transcendental_X

theorem noRingEquiv : ¬ Nonempty (A ≃+* B) := by
  rintro ⟨e⟩
  let t := algebraMap (RatFunc ℚ) B RatFunc.X
  have ha : IsAlgebraic ℚ (e.symm t) := Algebra.IsAlgebraic.isAlgebraic _
  have hb : IsAlgebraic ℚ t := by
    have h := ha.algHom e.toRatAlgEquiv.toAlgHom
    simpa [t] using h
  exact transcendentalInB hb

theorem cardinalA : Cardinal.mk A = Cardinal.aleph0 := by
  apply le_antisymm
  · simpa [Cardinal.mk_eq_aleph0 ℚ] using
      Algebra.IsAlgebraic.cardinalMk_le_max ℚ A
  · exact Cardinal.aleph0_le_mk A

theorem cardinalRatFunc : Cardinal.mk (RatFunc ℚ) = Cardinal.aleph0 := by
  have h : Cardinal.mk (RatFunc ℚ) = Cardinal.mk (Polynomial ℚ) :=
    IsFractionRing.cardinalMk (R := Polynomial ℚ) (RatFunc ℚ)
  rw [h]
  apply le_antisymm
  · exact (Polynomial.cardinalMk_le_max (R := ℚ)).trans (by simp)
  · exact Cardinal.aleph0_le_mk (Polynomial ℚ)

theorem cardinalB : Cardinal.mk B = Cardinal.aleph0 := by
  apply le_antisymm
  · simpa [cardinalRatFunc] using
      Algebra.IsAlgebraic.cardinalMk_le_max (RatFunc ℚ) B
  · exact Cardinal.aleph0_le_mk B

theorem equalCardinality : Cardinal.mk A = Cardinal.mk B := cardinalA.trans cardinalB.symm

theorem counterexample :
    Cardinal.mk A = Cardinal.mk B ∧
    FirstOrder.Language.ElementarilyEquivalent FirstOrder.Language.ring A B ∧
    ¬ Nonempty (A ≃+* B) :=
  ⟨equalCardinality, elementaryEquivalent, noRingEquiv⟩

end LevchukPapers.L2018Malcev

#print axioms LevchukPapers.L2018Malcev.elementaryEquivalent
#print axioms LevchukPapers.L2018Malcev.transcendentalInB
#print axioms LevchukPapers.L2018Malcev.noRingEquiv
#print axioms LevchukPapers.L2018Malcev.cardinalA
#print axioms LevchukPapers.L2018Malcev.cardinalRatFunc
#print axioms LevchukPapers.L2018Malcev.cardinalB
#print axioms LevchukPapers.L2018Malcev.equalCardinality
#print axioms LevchukPapers.L2018Malcev.counterexample
