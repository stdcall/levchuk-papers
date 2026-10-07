import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.NoncommRing

/- Limited steps from the adjoint-ring arguments, not the full paper.
   R corresponds to the associative ring L or NT(n,K).
   S corresponds to rho^-1(H); its additive-subgroup hypothesis is the
   conclusion of Theorem 4(a), and adjoint closure comes from H being a group.
   No nilpotence is needed for either of these two local algebraic steps. -/
namespace LevchukPapers1974

def adjoint {R : Type*} [NonUnitalRing R] (a b : R) : R := a + b + a * b

theorem adjoint_assoc {R : Type*} [NonUnitalRing R] (a b c : R) :
    adjoint (adjoint a b) c = adjoint a (adjoint b c) := by
  unfold adjoint
  noncomm_ring

theorem mul_mem_of_adjoint_closed {R : Type*} [NonUnitalRing R]
    (S : AddSubgroup R)
    (closed : ∀ a b : R, a ∈ S → b ∈ S → adjoint a b ∈ S)
    {a b : R} (ha : a ∈ S) (hb : b ∈ S) : a * b ∈ S := by
  have h := S.sub_mem (closed a b ha hb) (S.add_mem ha hb)
  have heq : adjoint a b - (a + b) = a * b := by
    unfold adjoint
    noncomm_ring
  rwa [heq] at h

#print axioms adjoint_assoc
#print axioms mul_mem_of_adjoint_closed
end LevchukPapers1974
