import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharP.Reduced
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring

namespace LevchukPapers.Enumeration1996.C2

@[ext] structure Coordinates (R : Type*) where
  s : R
  t : R
  u : R
  v : R
  deriving DecidableEq

variable {R : Type*} [CommRing R] [CharP R 2]

/-- Ordered root coordinates a(s)b(t)c(u)d(v) in characteristic two.
The correspondence to symplectic matrices is checked separately in Sage. -/
def mul (x y : Coordinates R) : Coordinates R :=
  ⟨x.s+y.s, x.t+y.t, x.u+y.u+y.s*x.t,
   x.v+y.v+y.s^2*x.t⟩

def graph (x : Coordinates R) : Coordinates R :=
  ⟨x.t,x.s^2,x.v+x.t*x.s^2,x.u^2+x.t^2*x.s^2⟩

def square (x : Coordinates R) : Coordinates R :=
  ⟨x.s^2,x.t^2,x.u^2,x.v^2⟩

theorem graph_mul (x y : Coordinates R) :
    graph (mul x y) = mul (graph x) (graph y) := by
  have htwo : (2 : R) = 0 := CharP.cast_eq_zero R 2
  have hfour : (4 : R) = 0 := by
    calc
      (4 : R) = 2+2 := by ring
      _ = 0 := by rw [htwo]; ring
  ext <;> simp only [graph, mul]
  all_goals ring_nf
  all_goals simp [htwo, hfour]

theorem graph_square (x : Coordinates R) : graph (graph x) = square x := by
  have htwo : (2 : R) = 0 := CharP.cast_eq_zero R 2
  ext <;> simp only [graph, square]
  all_goals ring_nf
  all_goals simp [htwo]

theorem mul_assoc (x y z : Coordinates R) :
    mul (mul x y) z = mul x (mul y z) := by
  have htwo : (2 : R) = 0 := CharP.cast_eq_zero R 2
  ext <;> simp only [mul]
  all_goals ring_nf
  all_goals simp [htwo]

def shortCentral (x : Coordinates R) : Prop :=
  x.s = 0 ∧ x.t = 0 ∧ x.v = 0

omit [CharP R 2] in
theorem graph_moves_short_central [Nontrivial R] :
    shortCentral (⟨0,0,1,0⟩ : Coordinates R) ∧
    ¬ shortCentral (graph (⟨0,0,1,0⟩ : Coordinates R)) := by
  simp [shortCentral, graph]

theorem square_injective {K : Type*} [Field K] [CharP K 2] :
    Function.Injective (square (R := K)) := by
  intro x y h
  ext
  all_goals apply frobenius_inj K 2
  · exact congrArg Coordinates.s h
  · exact congrArg Coordinates.t h
  · exact congrArg Coordinates.u h
  · exact congrArg Coordinates.v h

/-- Every finite field of characteristic two, without a perfectness
axiom or a stipulated x⁴=x identity. Existence of square roots follows
from finiteness and reducedness in the imported theorem. -/
theorem graph_bijective {K : Type*} [Field K] [CharP K 2] [Finite K] :
    Function.Bijective (graph (R := K)) := by
  constructor
  · intro x y h
    apply square_injective
    rw [← graph_square, ← graph_square, h]
  · intro y
    obtain ⟨s,hs⟩ := isSquare_of_charTwo' y.s
    obtain ⟨t,ht⟩ := isSquare_of_charTwo' y.t
    obtain ⟨u,hu⟩ := isSquare_of_charTwo' y.u
    obtain ⟨v,hv⟩ := isSquare_of_charTwo' y.v
    refine ⟨graph ⟨s,t,u,v⟩, ?_⟩
    rw [graph_square]
    ext <;> simp only [square]
    · exact (hs.trans (pow_two s).symm).symm
    · exact (ht.trans (pow_two t).symm).symm
    · exact (hu.trans (pow_two u).symm).symm
    · exact (hv.trans (pow_two v).symm).symm

end LevchukPapers.Enumeration1996.C2

#print axioms LevchukPapers.Enumeration1996.C2.graph_mul
#print axioms LevchukPapers.Enumeration1996.C2.graph_square
#print axioms LevchukPapers.Enumeration1996.C2.mul_assoc
#print axioms LevchukPapers.Enumeration1996.C2.graph_moves_short_central
#print axioms LevchukPapers.Enumeration1996.C2.square_injective
#print axioms LevchukPapers.Enumeration1996.C2.graph_bijective
