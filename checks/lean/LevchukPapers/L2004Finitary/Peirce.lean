import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel
import Mathlib.Data.Set.Basic

/- One-sided Peirce decomposition in Lemma 3.2. The coefficient ring is
   arbitrary and need not be commutative. No classification is asserted. -/
namespace LevchukPapers.L2004Finitary

variable {K : Type*} [Ring K]

theorem decomposition_idempotent {f₁ f₂ g₁ g₂ : K}
    (hf : f₁ + f₂ = 1) (hg : g₁ + g₂ = 1)
    (h₁ : f₁ * g₁ = 0) (h₂ : f₂ * g₂ = 0) :
    f₁ = g₂ ∧ f₂ = g₁ ∧ f₁ * f₁ = f₁ := by
  have hfg : f₁ = f₁ * g₂ := by
    calc
      f₁ = f₁ * (g₁ + g₂) := by rw [hg, mul_one]
      _ = f₁ * g₂ := by rw [mul_add, h₁, zero_add]
  have hgf : g₂ = f₁ * g₂ := by
    calc
      g₂ = (f₁ + f₂) * g₂ := by rw [hf, one_mul]
      _ = f₁ * g₂ := by rw [add_mul, h₂, add_zero]
  have h : f₁ = g₂ := hfg.trans hgf.symm
  have h' : f₂ = g₁ := by
    have he : g₂ + f₂ = g₂ + g₁ := by
      calc
        g₂ + f₂ = 1 := by rw [← h, hf]
        _ = g₂ + g₁ := by rw [add_comm g₂, hg]
    exact add_left_cancel he
  exact ⟨h, h', by simpa [h] using hfg.symm⟩

theorem fixed_points_range {f : K} (h : f * f = f) :
    {x : K | x * f = x} = Set.range (fun x : K => x * f) := by
  ext x
  constructor
  · intro hx
    exact ⟨x, hx⟩
  · rintro ⟨y, rfl⟩
    simp [mul_assoc, h]

theorem left_fixed_points_range {f : K} (h : f * f = f) :
    {x : K | f * x = x} = Set.range (fun x : K => f * x) := by
  ext x
  constructor
  · intro hx
    exact ⟨x, hx⟩
  · rintro ⟨y, rfl⟩
    simp [← mul_assoc, h]

theorem complementary_idempotent {f : K} (h : f * f = f) :
    (1 - f) * (1 - f) = 1 - f := by
  noncomm_ring [h]

theorem peirce_sets (A₁ A₂ B₁ B₂ : Set K)
    (hA : ∀ x, ∃ a ∈ A₁, ∃ b ∈ A₂, a + b = x)
    (hB : ∀ x, ∃ a ∈ B₁, ∃ b ∈ B₂, a + b = x)
    (h₁ : ∀ a ∈ A₁, ∀ b ∈ B₁, a * b = 0)
    (h₂ : ∀ a ∈ A₂, ∀ b ∈ B₂, a * b = 0) :
    ∃ f : K, f * f = f ∧
      A₁ = Set.range (fun x : K => x * f) ∧
      A₂ = Set.range (fun x : K => x * (1 - f)) ∧
      B₁ = Set.range (fun x : K => (1 - f) * x) ∧
      B₂ = Set.range (fun x : K => f * x) := by
  obtain ⟨f₁, hf₁, f₂, hf₂, hf⟩ := hA 1
  obtain ⟨g₁, hg₁, g₂, hg₂, hg⟩ := hB 1
  obtain ⟨he, he', hi⟩ := decomposition_idempotent hf hg
    (h₁ _ hf₁ _ hg₁) (h₂ _ hf₂ _ hg₂)
  have hc : f₂ = 1 - f₁ := by rw [eq_sub_iff_add_eq, add_comm, hf]
  have hb : g₁ = 1 - f₁ := he'.symm.trans hc
  have ha₁ : ∀ a ∈ A₁, a * f₁ = a := by
    intro a ha
    calc
      a * f₁ = a * g₂ := by rw [he]
      _ = a * (g₁ + g₂) := by rw [mul_add, h₁ _ ha _ hg₁, zero_add]
      _ = a := by rw [hg, mul_one]
  have ha₂ : ∀ a ∈ A₂, a * f₁ = 0 := by
    intro a ha
    rw [he]
    exact h₂ _ ha _ hg₂
  have hba₁ : ∀ b ∈ B₁, f₁ * b = 0 := by
    intro b hb'
    exact h₁ _ hf₁ _ hb'
  have hba₂ : ∀ b ∈ B₂, f₁ * b = b := by
    intro b hb'
    calc
      f₁ * b = (f₁ + f₂) * b := by rw [add_mul, h₂ _ hf₂ _ hb', add_zero]
      _ = b := by rw [hf, one_mul]
  refine ⟨f₁, hi, ?_, ?_, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      exact ⟨x, ha₁ _ hx⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨a, ha, b, hb', hy⟩ := hA y
      have hyf : y * f₁ = a := by rw [← hy, add_mul, ha₁ _ ha, ha₂ _ hb', add_zero]
      change y * f₁ ∈ A₁
      rwa [hyf]
  · ext x
    constructor
    · intro hx
      refine ⟨x, ?_⟩
      change x * (1 - f₁) = x
      rw [mul_sub, mul_one, ha₂ _ hx, sub_zero]
    · rintro ⟨y, rfl⟩
      obtain ⟨a, ha, b, hb', hy⟩ := hA y
      have hyf : y * (1 - f₁) = b := by
        rw [mul_sub, mul_one, ← hy, add_mul, ha₁ _ ha, ha₂ _ hb', add_zero]
        abel
      change y * (1 - f₁) ∈ A₂
      rwa [hyf]
  · ext x
    constructor
    · intro hx
      refine ⟨x, ?_⟩
      change (1 - f₁) * x = x
      rw [sub_mul, one_mul, hba₁ _ hx, sub_zero]
    · rintro ⟨y, rfl⟩
      obtain ⟨a, ha, b, hb', hy⟩ := hB y
      have hyf : (1 - f₁) * y = a := by
        rw [sub_mul, one_mul, ← hy, mul_add, hba₁ _ ha, hba₂ _ hb', zero_add]
        abel
      change (1 - f₁) * y ∈ B₁
      rwa [hyf]
  · ext x
    constructor
    · intro hx
      exact ⟨x, hba₂ _ hx⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨a, ha, b, hb', hy⟩ := hB y
      have hyf : f₁ * y = b := by rw [← hy, mul_add, hba₁ _ ha, hba₂ _ hb', zero_add]
      change f₁ * y ∈ B₂
      rwa [hyf]

theorem central_of_equal_one_sided_ideals {f : K} (hi : f * f = f)
    (h : Set.range (fun x : K => x * f) = Set.range (fun x : K => f * x)) :
    ∀ x : K, f * x = x * f := by
  intro x
  have hx : f * x ∈ Set.range (fun y : K => y * f) := by
    rw [h]
    exact ⟨x, rfl⟩
  have hy : x * f ∈ Set.range (fun y : K => f * y) := by
    rw [← h]
    exact ⟨x, rfl⟩
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  calc
    f * x = (f * x) * f := by rw [← ha, mul_assoc, hi]
    _ = f * (x * f) := mul_assoc _ _ _
    _ = x * f := by rw [← hb, ← mul_assoc, hi]

end LevchukPapers.L2004Finitary

#print axioms LevchukPapers.L2004Finitary.decomposition_idempotent
#print axioms LevchukPapers.L2004Finitary.fixed_points_range
#print axioms LevchukPapers.L2004Finitary.left_fixed_points_range
#print axioms LevchukPapers.L2004Finitary.complementary_idempotent
#print axioms LevchukPapers.L2004Finitary.peirce_sets
#print axioms LevchukPapers.L2004Finitary.central_of_equal_one_sided_ideals
