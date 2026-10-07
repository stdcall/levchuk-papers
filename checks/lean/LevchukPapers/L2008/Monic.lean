import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.NoncommRing

/-!
Restricted algebraic step for `lem:l2008-monic-nilpotent-monic-invertible`:
an endomorphism `1 + N` is invertible when its correction operator has cube
zero. This is the finite-filtration inverse underlying Lemma 3; it is not
a formalization of the article's tame automorphism algorithms.
-/
namespace LevchukPapers2008Monic

theorem cubic_inverse_left {A : Type*} [Ring A] (N : A) (h : N ^ 3 = 0) :
    (1 - N + N ^ 2) * (1 + N) = 1 := by
  calc
    (1 - N + N ^ 2) * (1 + N) = 1 + N ^ 3 := by noncomm_ring
    _ = 1 := by rw [h]; simp

theorem cubic_inverse_right {A : Type*} [Ring A] (N : A) (h : N ^ 3 = 0) :
    (1 + N) * (1 - N + N ^ 2) = 1 := by
  calc
    (1 + N) * (1 - N + N ^ 2) = 1 + N ^ 3 := by noncomm_ring
    _ = 1 := by rw [h]; simp

theorem cubic_monic_bijective {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (N : Module.End K V) (h : N ^ 3 = 0) :
    Function.Bijective ((1 + N : Module.End K V) : V → V) := by
  let f : Module.End K V := 1 + N
  let g : Module.End K V := 1 - N + N ^ 2
  have hgf : g * f = 1 := cubic_inverse_left N h
  have hfg : f * g = 1 := cubic_inverse_right N h
  constructor
  · intro x y hxy
    have hx : g (f x) = x := by
      have t := congrArg (fun u : Module.End K V => u x) hgf
      simpa using t
    have hy : g (f y) = y := by
      have t := congrArg (fun u : Module.End K V => u y) hgf
      simpa using t
    calc
      x = g (f x) := hx.symm
      _ = g (f y) := congrArg g hxy
      _ = y := hy
  · intro y
    refine ⟨g y, ?_⟩
    change f (g y) = y
    have t := congrArg (fun u : Module.End K V => u y) hfg
    simpa using t

end LevchukPapers2008Monic

#print axioms LevchukPapers2008Monic.cubic_inverse_left
#print axioms LevchukPapers2008Monic.cubic_inverse_right
#print axioms LevchukPapers2008Monic.cubic_monic_bijective
