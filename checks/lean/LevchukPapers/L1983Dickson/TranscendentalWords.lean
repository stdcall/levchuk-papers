import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Data.Matrix.Basic

/- Proposition1, printed pp.432–433: the transcendence step.
The nonzero polynomial off-diagonal entry is a separate hypothesis.
The leading-term induction for reduced words is not silently assumed
to have been formalized here. -/
namespace LevchukPapers.L1983Dickson

theorem transcendental_evaluation_nonzero {R A : Type*}
    [CommRing R] [Ring A] [Algebra R A]
    (x : A) (hx : Transcendental R x) (p : Polynomial R) (hp : p ≠ 0) :
    Polynomial.aeval x p ≠ 0 := by
  intro h
  exact hp ((transcendental_iff.mp hx) p h)

theorem polynomial_matrix_not_scalar {R A : Type*}
    [CommRing R] [Ring A] [Algebra R A]
    (x : A) (hx : Transcendental R x)
    (M : Matrix (Fin 2) (Fin 2) (Polynomial R)) (hp : M 0 1 ≠ 0) (s : A) :
    (fun i j => Polynomial.aeval x (M i j)) ≠
      (fun i j => if i=j then s else 0) := by
  intro heq
  have h := congrFun (congrFun heq 0) 1
  have hzero : Polynomial.aeval x (M 0 1)=0 := by simpa using h
  exact transcendental_evaluation_nonzero x hx (M 0 1) hp hzero

end LevchukPapers.L1983Dickson

#print axioms LevchukPapers.L1983Dickson.transcendental_evaluation_nonzero
#print axioms LevchukPapers.L1983Dickson.polynomial_matrix_not_scalar
