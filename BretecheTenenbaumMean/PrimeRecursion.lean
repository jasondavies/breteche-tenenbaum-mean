module

public import BretecheTenenbaumMean.OrderedRecursion
public import BretecheTenenbaumMean.PrimeSums.Product

@[expose] public section

/-! # Iterated largest-prime recursion for the truncated moments -/

namespace BretecheTenenbaumMean

open Finset Real

/-- Restricting a prime cutoff further to integers below `p`. -/
theorem primesLT_filter_lt {x : ℝ} {p : ℕ} (hp : (p : ℝ) ≤ x) :
    (primesLT x).filter (fun r ↦ r < p) = primesLT p := by
  ext r
  simp only [mem_filter, mem_primesLT]
  constructor
  · rintro ⟨⟨hr, _⟩, hrp⟩
    exact ⟨hr, by exact_mod_cast hrp⟩
  · rintro ⟨hr, hrp⟩
    exact ⟨⟨hr, hrp.trans_le hp⟩, by exact_mod_cast hrp⟩

/-- Exact finite iteration of a recurrence with prime reciprocal weights. -/
theorem prime_recursion_le (A V : ℝ → ℝ)
    (hrec : ∀ x, A x ≤ V x + ∑ p ∈ primesLT x, A p / p) (x : ℝ) :
    A x ≤ V x + ∑ p ∈ primesLT x, (V p / p) *
      ∏ r ∈ (primesLT x).filter (fun r ↦ p < r), (1 + (r : ℝ)⁻¹) := by
  have h := sum_ordered_recursion_le (primesLT x) (fun p ↦ (p : ℝ)⁻¹)
    (fun p ↦ A p) (fun p ↦ V p) (fun _ _ ↦ by positivity) (fun p hp ↦ by
      rw [primesLT_filter_lt (mem_primesLT.1 hp).2.le]
      simpa only [div_eq_mul_inv, mul_comm] using hrec p)
  have hh := add_le_add (le_refl (V x)) h
  exact (hrec x).trans (by simpa only [div_eq_mul_inv, mul_comm] using hh)

/-- The tail Euler product is bounded by the ratio of normalizers. -/
theorem prime_tail_product_le {x : ℝ} {p : ℕ} (hp : (p : ℝ) ≤ x) :
    (∏ r ∈ (primesLT x).filter (fun r ↦ p < r), (1 + (r : ℝ)⁻¹)) ≤
      normalizer x / normalizer p := by
  classical
  let s := primesLT x
  have hsub : s.filter (fun r ↦ p < r) ⊆ s.filter (fun r ↦ ¬ r < p) := by
    intro r hr
    exact mem_filter.2 ⟨(mem_filter.1 hr).1, not_lt.2 (mem_filter.1 hr).2.le⟩
  have hle := prod_le_prod_of_subset_of_one_le₀
    (f := fun r : ℕ ↦ 1 + (r : ℝ)⁻¹) hsub (fun _ _ ↦ by positivity)
    (fun r _ _ ↦ by have := inv_nonneg.2 (Nat.cast_nonneg (α := ℝ) r); linarith)
  have he := prod_filter_mul_prod_filter_not s (fun r ↦ r < p)
    (fun r ↦ 1 + (r : ℝ)⁻¹)
  have hfirst : (∏ r ∈ s.filter (fun r ↦ r < p), (1 + (r : ℝ)⁻¹)) = normalizer p := by
    dsimp only [s]
    rw [primesLT_filter_lt hp]
    rfl
  rw [hfirst] at he
  apply (le_div_iff₀ (normalizer_pos p)).2
  have h := mul_le_mul_of_nonneg_left hle (normalizer_pos p).le
  rw [he] at h
  simpa only [normalizer, s, mul_comm] using h

/-- Positivity of the error term. -/
theorem recursionError_pos (δ T : ℝ) (θ : ℕ → ℝ) (q : ℕ) (x : ℝ) :
    0 < recursionError δ T θ q x := by
  unfold recursionError
  have h : 0 ≤ ∑ p ∈ primesLT x, ∑ m ∈ smoothSupport p,
      (momentGoodSet δ T θ (q - 1)).indicator (fun m ↦ mixedRemainder q m p / tau m) m /
        ((m : ℝ) * p) := by
    apply sum_nonneg
    intro p _
    apply sum_nonneg
    intro m _
    apply div_nonneg _ (by positivity)
    apply Set.indicator_nonneg _ m
    intro n _
    exact div_nonneg (sum_nonneg (fun j _ ↦ mul_nonneg (Nat.cast_nonneg _) (mixedMoment_nonneg _ _ _ _)))
      (Nat.cast_nonneg _)
  linarith

/-- The iterated recurrence with exact normalizers, before applying Mertens. -/
theorem truncatedMoment_le_recursionError (δ T : ℝ) (θ : ℕ → ℝ)
    {q : ℕ} (hq : 1 ≤ q) (x : ℝ) :
    truncatedMoment δ T θ q x ≤ recursionError δ T θ q x / normalizer x +
      ∑ p ∈ primesLT x, recursionError δ T θ q p / ((p : ℝ) * normalizer p) := by
  let V := recursionError δ T θ q
  have h := prime_recursion_le (fun y ↦ normalizer y * truncatedMoment δ T θ q y) V
    (fun y ↦ truncatedMoment_largest_prime_le δ T θ hq y) x
  have hbound : normalizer x * truncatedMoment δ T θ q x ≤
      V x + ∑ p ∈ primesLT x, (V p / p) * (normalizer x / normalizer p) := by
    refine h.trans (add_le_add le_rfl (sum_le_sum (fun p hp ↦ ?_)))
    exact mul_le_mul_of_nonneg_left (prime_tail_product_le (mem_primesLT.1 hp).2.le)
      (div_nonneg (recursionError_pos δ T θ q p).le (Nat.cast_nonneg p))
  have hh : truncatedMoment δ T θ q x ≤
      (V x + ∑ p ∈ primesLT x, (V p / p) * (normalizer x / normalizer p)) / normalizer x :=
    (le_div_iff₀ (normalizer_pos x)).2 (by simpa only [mul_comm] using hbound)
  convert hh using 1
  rw [add_div, sum_div]
  congr 1
  apply sum_congr rfl
  intro p _
  dsimp only [V]
  field_simp [(normalizer_pos x).ne']

/-- Equation (2.15): the iterated largest-prime bound, with one absolute
constant uniform in the moment order, penalty and threshold data. -/
theorem truncatedMoment_recursion_bound : ∃ C > 0, ∀ δ T (θ : ℕ → ℝ) (q : ℕ) (x : ℝ),
    1 ≤ q → 2 ≤ x →
    truncatedMoment δ T θ q x ≤ C * (recursionError δ T θ q x / log x +
      ∑ p ∈ primesLT x, recursionError δ T θ q p / ((p : ℝ) * log p)) := by
  obtain ⟨c, _, hc, _, hnormal⟩ := PrimeSums.normalizer_bounds
  refine ⟨c⁻¹, inv_pos.2 hc, fun δ T θ q x hq hx ↦ ?_⟩
  have hlog : ∀ y : ℝ, 2 ≤ y → 0 < log y := fun y hy ↦ log_pos (by linarith)
  have hV : ∀ y : ℝ, 2 ≤ y →
      recursionError δ T θ q y / normalizer y ≤ c⁻¹ * (recursionError δ T θ q y / log y) := by
    intro y hy
    calc
      _ ≤ recursionError δ T θ q y / (c * log y) :=
        div_le_div_of_nonneg_left (recursionError_pos δ T θ q y).le
          (mul_pos hc (hlog y hy)) (hnormal y hy).1
      _ = _ := by ring
  calc
    _ ≤ recursionError δ T θ q x / normalizer x +
        ∑ p ∈ primesLT x, recursionError δ T θ q p / ((p : ℝ) * normalizer p) :=
      truncatedMoment_le_recursionError δ T θ hq x
    _ ≤ c⁻¹ * (recursionError δ T θ q x / log x) +
        ∑ p ∈ primesLT x, c⁻¹ * (recursionError δ T θ q p / ((p : ℝ) * log p)) := by
      apply add_le_add (hV x hx)
      apply sum_le_sum
      intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_primesLT.1 hp).1.two_le
      have h := div_le_div_of_nonneg_right (hV p hp2) (Nat.cast_nonneg p)
      convert h using 1 <;> ring
    _ = _ := by rw [← mul_sum, ← mul_add]

end BretecheTenenbaumMean
