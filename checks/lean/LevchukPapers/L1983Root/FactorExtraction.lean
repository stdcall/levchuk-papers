import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Data.Int.GCD

/- The subgroup argument in Lemma 1, pp.506–508. The root relations
must be supplied separately. No Chevalley commutator is assumed to have
been formalized by these lemmas. The exponent m is char(K), and n is
the integer coefficient to be removed; Nat.Coprime n m is precisely the
printed gcd restriction, including its meaning when char(K)=0. -/
namespace LevchukPapers.L1983Root

theorem coprime_power_mem {G : Type*} [Group G] (H : Subgroup G)
    (x : G) (n m : ℕ) (hcop : Nat.Coprime n m)
    (hpow : x ^ n ∈ H) (hexp : x ^ m = 1) : x ∈ H := by
  have hn : x ^ (n : ℤ) ∈ H := by simpa using hpow
  have hm : x ^ (m : ℤ) ∈ H := by simp [hexp]
  have hbez : (1 : ℤ) = n * Nat.gcdA n m + m * Nat.gcdB n m := by
    simpa [hcop.gcd_eq_one] using (Nat.gcd_eq_gcd_ab n m)
  have h : x ^ (1 : ℤ) ∈ H := by
    rw [hbez, zpow_add, zpow_mul, zpow_mul]
    exact H.mul_mem (H.zpow_mem hn _) (H.zpow_mem hm _)
  simpa using h

theorem four_factor_extraction {G : Type*} [Group G]
    (H : Subgroup G) (c d e f g : G) (m : ℕ)
    (h2 : Nat.Coprime 2 m) (h6 : Nat.Coprime 6 m)
    (hdexp : d ^ m = 1) (heexp : e ^ m = 1) (hfexp : f ^ m = 1)
    (hproduct : c * d * e * f ∈ H)
    (he6 : e ^ 6 ∈ H) (hf6 : f ^ 6 ∈ H)
    (hd2g : d ^ 2 * g ∈ H) (hg : g ∈ H) :
    c ∈ H ∧ d ∈ H ∧ e ∈ H ∧ f ∈ H := by
  have he := coprime_power_mem H e 6 m h6 he6 heexp
  have hf := coprime_power_mem H f 6 m h6 hf6 hfexp
  have hd2 : d ^ 2 ∈ H := (H.mul_mem_cancel_right hg).mp hd2g
  have hd := coprime_power_mem H d 2 m h2 hd2 hdexp
  have hcde : c * d * e ∈ H := (H.mul_mem_cancel_right hf).mp hproduct
  have hcd : c * d ∈ H := (H.mul_mem_cancel_right he).mp hcde
  have hc : c ∈ H := (H.mul_mem_cancel_right hd).mp hcd
  exact ⟨hc, hd, he, hf⟩

/-- The convention which simultaneously fits the printed (2)–(4). -/
def rootComm {G : Type*} [Group G] (x y : G) : G := y⁻¹ * x⁻¹ * y * x

theorem rootComm_mem {G : Type*} [Group G] (H : Subgroup G)
    {x y : G} (hx : x ∈ H) (hy : y ∈ H) : rootComm x y ∈ H :=
  H.mul_mem (H.mul_mem (H.mul_mem (H.inv_mem hy) (H.inv_mem hx)) hy) hx

/-- The entire subgroup extraction for the first triality case, after
the explicit root relations have been supplied. In the matrix model,
c=C(-ut), d=D(uσ(u)t), e=E(-N(u)t), f=F(-N(u)t²).
Sage verifies exactly these relation hypotheses in the integral model;
Lean proves their consequence for any group and every parameter. -/
theorem triality_factor_extraction {G : Type*} [Group G]
    (H : Subgroup G) (a b c d e f : G) (m : ℕ)
    (ha : a ∈ H) (hb : b ∈ H)
    (h2 : Nat.Coprime 2 m) (h6 : Nat.Coprime 6 m)
    (hdexp : d ^ m = 1) (heexp : e ^ m = 1) (hfexp : f ^ m = 1)
    (hproduct : rootComm a b = c * d * e * f)
    (hdouble : (rootComm (rootComm a b) a)⁻¹ = d ^ 2 * e ^ 6 * f ^ 3)
    (htriple : rootComm (rootComm (rootComm a b) a) a = e ^ 6)
    (hfourth : rootComm (rootComm (rootComm (rootComm a b) a) a) b = f ^ 6) :
    c ∈ H ∧ d ∈ H ∧ e ∈ H ∧ f ∈ H := by
  have h0 := rootComm_mem H ha hb
  have h1 := rootComm_mem H h0 ha
  have h2mem := rootComm_mem H h1 ha
  have h3mem := rootComm_mem H h2mem hb
  have he6 : e ^ 6 ∈ H := htriple ▸ h2mem
  have hf6 : f ^ 6 ∈ H := hfourth ▸ h3mem
  have hf := coprime_power_mem H f 6 m h6 hf6 hfexp
  have hg : e ^ 6 * f ^ 3 ∈ H := H.mul_mem he6 (H.pow_mem hf 3)
  have hd2g : d ^ 2 * (e ^ 6 * f ^ 3) ∈ H := by
    rw [← mul_assoc, ← hdouble]
    exact H.inv_mem h1
  exact four_factor_extraction H c d e f (e ^ 6 * f ^ 3) m h2 h6
    hdexp heexp hfexp (hproduct ▸ h0) he6 hf6 hd2g hg

end LevchukPapers.L1983Root

#print axioms LevchukPapers.L1983Root.coprime_power_mem
#print axioms LevchukPapers.L1983Root.four_factor_extraction
#print axioms LevchukPapers.L1983Root.rootComm_mem
#print axioms LevchukPapers.L1983Root.triality_factor_extraction
