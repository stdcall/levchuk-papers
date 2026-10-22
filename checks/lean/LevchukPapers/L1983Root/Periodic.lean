import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.CharP.Reduced
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
Scalar descent used in sections 3 and 5 of the 1983 article.
`frobeniusPeriodic` states the explicit finite Frobenius-orbit property.
It is derived below from multiplicative torsion using injectivity of
Frobenius on the finite group of d-th roots of unity. This proves scalar
descent, rather than the Chevalley/Steinberg classification theorem.
-/
namespace LevchukPapers.L1983Root

variable {K : Type*} [Field K]

def FrobeniusPeriodic (F : Subfield K) (p : ℕ) : Prop :=
  ∀ x ∈ F, ∃ k : ℕ, x ^ (p ^ (k + 1)) = x

theorem frobenius_periodic_of_torsion (F : Subfield K) (p : ℕ)
    [ExpChar K p]
    (htorsion : ∀ x ∈ F, x ≠ 0 → ∃ d : ℕ, 0 < d ∧ x ^ d = 1) :
    FrobeniusPeriodic F p := by
  intro x hx
  by_cases hzero : x = 0
  · subst x
    exact ⟨0, by simpa using (zero_pow (Nat.ne_of_gt (expChar_pos K p)) :
      (0 : K) ^ p = 0)⟩
  obtain ⟨d, hd, hxd⟩ := htorsion x hx hzero
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  let u : rootsOfUnity d K :=
    ⟨Units.mk0 x hzero, (mem_rootsOfUnity' d _).mpr hxd⟩
  let f : rootsOfUnity d K → rootsOfUnity d K := fun z => z ^ p
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Units.ext
    apply frobenius_inj K p
    exact congrArg (fun z : rootsOfUnity d K => ((z : Kˣ) : K)) hab
  obtain ⟨n, hn, heq⟩ := Function.mem_periodicPts.mp (hf.mem_periodicPts u)
  have hi : ∀ n : ℕ, ((f^[n] u : Kˣ) : K) = x ^ (p ^ n) := by
    intro n
    induction n with
    | zero => simp [u]
    | succ n ih =>
      simp only [Function.iterate_succ_apply', f, SubgroupClass.coe_pow,
        Units.val_pow_eq_pow_val, ih]
      rw [← pow_mul, Nat.pow_succ]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  refine ⟨k, ?_⟩
  rw [← hi]
  exact congrArg (fun z : rootsOfUnity d K => ((z : Kˣ) : K)) heq

theorem subfield_eq_of_power_mem
    (P F : Subfield K) (p : ℕ)
    (hPF : P ≤ F)
    (hperiodic : FrobeniusPeriodic F p)
    (hpower : ∀ x ∈ F, x ^ p ∈ P) : F = P := by
  apply le_antisymm ?_ hPF
  intro x hx
  obtain ⟨k, hk⟩ := hperiodic x hx
  have hm : (x ^ p) ^ (p ^ k) ∈ P := P.pow_mem (hpower x hx) _
  rw [← pow_mul, ← Nat.pow_succ'] at hm
  rwa [hk] at hm

theorem square_subfield_descent
    (P F : Subfield K) (hPF : P ≤ F)
    (hperiodic : FrobeniusPeriodic F 2)
    (hpower : ∀ x ∈ F, x ^ 2 ∈ P) : F = P :=
  subfield_eq_of_power_mem P F 2 hPF hperiodic hpower

theorem cube_subfield_descent
    (P F : Subfield K) (hPF : P ≤ F)
    (hperiodic : FrobeniusPeriodic F 3)
    (hpower : ∀ x ∈ F, x ^ 3 ∈ P) : F = P :=
  subfield_eq_of_power_mem P F 3 hPF hperiodic hpower

theorem subfield_eq_of_torsion_and_power_mem
    (P F : Subfield K) (p : ℕ) [ExpChar K p]
    (hPF : P ≤ F)
    (htorsion : ∀ x ∈ F, x ≠ 0 → ∃ d : ℕ, 0 < d ∧ x ^ d = 1)
    (hpower : ∀ x ∈ F, x ^ p ∈ P) : F = P :=
  subfield_eq_of_power_mem P F p hPF
    (frobenius_periodic_of_torsion F p htorsion) hpower

theorem torsion_of_power_mem
    (P F : Subfield K) (p : ℕ) (hp : 0 < p)
    (hPtorsion : ∀ y ∈ P, y ≠ 0 → ∃ d : ℕ, 0 < d ∧ y ^ d = 1)
    (hpower : ∀ x ∈ F, x ^ p ∈ P) :
    ∀ x ∈ F, x ≠ 0 → ∃ d : ℕ, 0 < d ∧ x ^ d = 1 := by
  intro x hx hzero
  obtain ⟨d, hd, heq⟩ := hPtorsion (x ^ p) (hpower x hx) (pow_ne_zero _ hzero)
  exact ⟨p * d, Nat.mul_pos hp hd, by rw [pow_mul, heq]⟩

theorem subfield_eq_of_torsion_target_and_power_mem
    (P F : Subfield K) (p : ℕ) [ExpChar K p]
    (hPF : P ≤ F)
    (hPtorsion : ∀ y ∈ P, y ≠ 0 → ∃ d : ℕ, 0 < d ∧ y ^ d = 1)
    (hpower : ∀ x ∈ F, x ^ p ∈ P) : F = P :=
  subfield_eq_of_torsion_and_power_mem P F p hPF
    (torsion_of_power_mem P F p (expChar_pos K p) hPtorsion hpower) hpower

end LevchukPapers.L1983Root

#print axioms LevchukPapers.L1983Root.subfield_eq_of_power_mem
#print axioms LevchukPapers.L1983Root.square_subfield_descent
#print axioms LevchukPapers.L1983Root.cube_subfield_descent
#print axioms LevchukPapers.L1983Root.frobenius_periodic_of_torsion
#print axioms LevchukPapers.L1983Root.subfield_eq_of_torsion_and_power_mem
#print axioms LevchukPapers.L1983Root.torsion_of_power_mem
#print axioms LevchukPapers.L1983Root.subfield_eq_of_torsion_target_and_power_mem
