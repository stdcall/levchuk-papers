import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NoncommRing

/- Local algebraic steps only. The zero hypotheses below are precisely the
triangular support identities for u=x e_il, v=y e_lj, i>l>j, b in NT.
No claim is made here about the classification theorem or infinite chains. -/
namespace LevchukPapers1987

def lie {R : Type*} [NonUnitalRing R] (a b : R) : R := a*b-b*a

theorem double_lie {R : Type*} [NonUnitalRing R] (u v b : R)
    (hu : u*b*v=0) (hv : v*b*u=0) (hvu : v*u=0) :
    lie u (lie v b) = (u*v)*b := by
  unfold lie
  calc
    u*(v*b-b*v)-(v*b-b*v)*u =
      (u*v)*b-u*b*v-v*b*u+b*(v*u) := by noncomm_ring
    _ = (u*v)*b := by rw [hu, hv, hvu, mul_zero]; noncomm_ring

/- The intersection Aut(adj R) ∩ Aut(Lie R) contains additive maps:
on an abelian ideal the group law is addition. Once additivity and preservation
of the adjoint operation are established, multiplicativity follows locally. -/
theorem mul_preserved {R S : Type*} [NonUnitalRing R] [NonUnitalRing S]
    (f : R →+ S)
    (hadj : ∀ a b, f (a+b+a*b)=f a+f b+f a*f b)
    (a b : R) : f (a*b)=f a*f b := by
  have h := hadj a b
  rw [map_add, map_add] at h
  exact add_left_cancel h

#print axioms double_lie
#print axioms mul_preserved
end LevchukPapers1987

