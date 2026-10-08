import Mathlib.RingTheory.PowerSeries.Inverse

/- Scope: the unit criterion used in Proposition 1, printed p. 228.
   The coefficient division ring need not be commutative. -/
namespace LevchukPapers.L2005Sylow

variable {K : Type*} [DivisionRing K]

theorem series_isUnit_iff (f : PowerSeries K) :
    IsUnit f ↔ PowerSeries.constantCoeff f ≠ 0 := by
  rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]

theorem indeterminate_not_isUnit :
    ¬ IsUnit (PowerSeries.X : PowerSeries K) := by
  rw [series_isUnit_iff]
  simp

theorem constant_one_isUnit :
    IsUnit (PowerSeries.C (1 : K)) := by
  rw [series_isUnit_iff]
  simp

end LevchukPapers.L2005Sylow

#print axioms LevchukPapers.L2005Sylow.series_isUnit_iff
#print axioms LevchukPapers.L2005Sylow.indeterminate_not_isUnit
#print axioms LevchukPapers.L2005Sylow.constant_one_isUnit
