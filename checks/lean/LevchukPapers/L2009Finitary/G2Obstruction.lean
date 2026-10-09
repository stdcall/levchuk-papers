import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.LinearAlgebra.Matrix.Notation
import Lean.Elab.Tactic.Omega

/- Final root-lattice step in Proposition 1. Coordinates are in the simple
root basis (a,b), a short and b long. An additive lattice map w has columns
(p,r),(q,s). The input w(a)=2a+b and preservation of the two-element set
{3a+b,3a+2b} force the impossible alternatives below. This proves only the
linear contradiction after (3.4); it does not prove the preceding Bruhat
reduction, maximal order, or uniqueness of the normal subgroup. -/
namespace Levchuk2009Finitary

def shortRoot : Fin 2 → Int := ![1, 0]
def longRoot : Fin 2 → Int := ![0, 1]

/- The actual lattice map is arbitrary and linear; no Weyl-group membership
is needed. The roots are a, b, 2a+b, 3a+b, 3a+2b in the source basis. -/
theorem g2_lattice_map_obstruction
    (w : Module.End Int (Fin 2 → Int))
    (ha : w shortRoot = (2 : Int) • shortRoot + longRoot)
    (hfirst : w ((3 : Int) • shortRoot + longRoot) = (3 : Int) • shortRoot + longRoot ∨
              w ((3 : Int) • shortRoot + longRoot) = (3 : Int) • shortRoot + (2 : Int) • longRoot)
    (hsecond : w ((3 : Int) • shortRoot + (2 : Int) • longRoot) = (3 : Int) • shortRoot + longRoot ∨
               w ((3 : Int) • shortRoot + (2 : Int) • longRoot) = (3 : Int) • shortRoot + (2 : Int) • longRoot) :
    False := by
  have h₁ : 6 + w longRoot 0 = 3 := by
    rcases hfirst with h | h
    all_goals
      rw [map_add, map_smul, ha] at h
      have hc := congrArg (fun v : Fin 2 → Int => v 0) h
      simpa [shortRoot, longRoot] using hc
  have h₂ : 6 + 2 * w longRoot 0 = 3 := by
    rcases hsecond with h | h
    all_goals
      rw [map_add, map_smul, map_smul, ha] at h
      have hc := congrArg (fun v : Fin 2 → Int => v 0) h
      simpa [shortRoot, longRoot] using hc
  omega

theorem g2_root_obstruction (p q r s : Int)
    (ha₁ : p = 2) (_ha₂ : r = 1)
    (_hfirst : (3*p+q = 3 ∧ 3*r+s = 1) ∨
              (3*p+q = 3 ∧ 3*r+s = 2))
    (hsecond : (3*p+2*q = 3 ∧ 3*r+2*s = 1) ∨
               (3*p+2*q = 3 ∧ 3*r+2*s = 2)) : False := by
  omega

#print axioms Levchuk2009Finitary.g2_root_obstruction
#print axioms Levchuk2009Finitary.g2_lattice_map_obstruction
end Levchuk2009Finitary
