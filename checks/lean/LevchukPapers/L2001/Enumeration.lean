import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace LevchukPapers2001Enumeration

/-- The numerator produced by combining the two contour integrals.
This is only the polynomial identity in (29)–(30), not an analytic
interchange of sums and integrals or a classification of ideals. -/
theorem combined_numerator {R : Type*} [CommRing R] (n x : R) :
    (n+1-2*(2*n+1)*x+2*(2*n+1)*x^2)
      + x*(n-4*n*x+2*(2*n+1)*x^2) =
    n+1-(3*n+2)*x+2*x^2+2*(2*n+1)*x^3 := by
  ring

/-- Algebraic branch calculation for the correction to Lemma 5.
z=x/[2(1+x)^2] and y=sqrt(1-8z) on the branch at zero are encoded
by explicit polynomial hypotheses. No assertion about convergence
or existence of this square-root branch is formalized here. -/
theorem corrected_branch_numerator {R : Type*} [CommRing R]
    (x z y : R) (hz : 2*z*(1+x)^2=x)
    (hy : y*(1+x)=1-x) :
    ((1-12*z+y)*(2-x)-4*(1-9*z))*(1+x)^2 = 0 := by
  linear_combination (6*(1+x))*hz + ((2-x)*(1+x))*hy

end LevchukPapers2001Enumeration

#print axioms LevchukPapers2001Enumeration.combined_numerator
#print axioms LevchukPapers2001Enumeration.corrected_branch_numerator
