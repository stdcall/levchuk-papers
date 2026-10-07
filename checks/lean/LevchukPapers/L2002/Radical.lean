import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing

namespace LevchukPapers2002Radical

/-- The adjoint product is associative in every associative ring. -/
theorem adjoint_associative {R : Type*} [Ring R] (a b c : R) :
    (a + b + a*b) + c + (a + b + a*b)*c =
    a + (b + c + b*c) + a*(b + c + b*c) := by
  noncomm_ring

/-- The precise unit calculation used to repair Lemma 3.1.
The hypotheses encode two successive choices afforded by 2F = F.
The inverse u is supplied explicitly; this lemma does not prove the
radical-ring inverse assertion or the normal-closure theorem. -/
theorem two_divisions_coefficient {R : Type*} [CommRing R]
    (z s r u : R) (hz : z = 2*s) (hs : s = 2*r)
    (hu : u*(1+r) = 1) : u*s*(2+s) = z := by
  rw [hz, hs]
  calc
    u*(2*r)*(2+2*r) = (u*(1+r))*(2*(2*r)) := by ring
    _ = 2*(2*r) := by rw [hu]; ring

end LevchukPapers2002Radical

#print axioms LevchukPapers2002Radical.adjoint_associative
#print axioms LevchukPapers2002Radical.two_divisions_coefficient
