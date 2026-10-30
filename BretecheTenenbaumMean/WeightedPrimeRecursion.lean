module

public import BretecheTenenbaumMean.WeightedLargestPrime
public import BretecheTenenbaumMean.PrimeRecursion

@[expose] public section

/-! # Finite iteration of the weighted largest-prime recurrence -/

namespace BretecheTenenbaumMean.WeightedModel

open Finset Real

/-- Exact finite iteration of a recurrence with prime reciprocal weights. -/
theorem prime_recursion_le (w : MultiplicativeWeight) (A V : ℝ → ℝ)
    (hrec : ∀ x, A x ≤ V x + ∑ p ∈ primesLT x, w p * A p / p) (x : ℝ) :
    A x ≤ V x + ∑ p ∈ primesLT x, (w p * V p / p) *
      ∏ r ∈ (primesLT x).filter (fun r ↦ p < r), (1 + w r / r) := by
  have h := sum_ordered_recursion_le (primesLT x) (fun p ↦ w p / p)
    (fun p ↦ A p) (fun p ↦ V p) (fun p _ ↦ div_nonneg (w.nonneg p) (Nat.cast_nonneg _)) (fun p hp ↦ by
      rw [primesLT_filter_lt (mem_primesLT.1 hp).2.le]
      simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hrec p)
  have hh := add_le_add (le_refl (V x)) h
  exact (hrec x).trans (by simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh)

/-- The tail Euler product is bounded by the ratio of normalizers. -/
theorem prime_tail_product_le (w : MultiplicativeWeight) {x : ℝ} {p : ℕ} (hp : (p : ℝ) ≤ x) :
    (∏ r ∈ (primesLT x).filter (fun r ↦ p < r), (1 + w r / r)) ≤
      normalizer w x / normalizer w p := by
  classical
  let s := primesLT x
  have hsub : s.filter (fun r ↦ p < r) ⊆ s.filter (fun r ↦ ¬ r < p) := by
    intro r hr
    exact mem_filter.2 ⟨(mem_filter.1 hr).1, not_lt.2 (mem_filter.1 hr).2.le⟩
  have hle := prod_le_prod_of_subset_of_one_le₀
    (f := fun r : ℕ ↦ 1 + w r / r) hsub (fun r _ ↦ by have := w.nonneg r; positivity)
    (fun r _ _ ↦ by have := div_nonneg (w.nonneg r) (Nat.cast_nonneg (α := ℝ) r); linarith)
  have he := prod_filter_mul_prod_filter_not s (fun r ↦ r < p)
    (fun r ↦ 1 + w r / r)
  have hfirst : (∏ r ∈ s.filter (fun r ↦ r < p), (1 + w r / r)) = normalizer w p := by
    dsimp only [s]
    rw [primesLT_filter_lt hp]
    rfl
  rw [hfirst] at he
  apply (le_div_iff₀ (normalizer_pos w p)).2
  have h := mul_le_mul_of_nonneg_left hle (normalizer_pos w p).le
  rw [he] at h
  simpa only [normalizer, s, mul_comm] using h

/-- Positivity of the error term. -/
theorem recursionError_pos (w : MultiplicativeWeight) (δ T : ℝ) (θ : ℕ → ℝ) (q : ℕ) (x : ℝ) :
    0 < recursionError w δ T θ q x := by
  unfold recursionError
  have h : 0 ≤ ∑ p ∈ primesLT x, ∑ m ∈ smoothSupport p,
      w p * w m * (momentGoodSet δ T θ (q - 1)).indicator (fun m ↦ mixedRemainder q m p / tau m) m /
        ((m : ℝ) * p) := by
    apply sum_nonneg
    intro p _
    apply sum_nonneg
    intro m _
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (mul_nonneg (w.nonneg p) (w.nonneg m))
    apply Set.indicator_nonneg _ m
    intro n _
    exact div_nonneg (sum_nonneg (fun j _ ↦ mul_nonneg (Nat.cast_nonneg _) (mixedMoment_nonneg _ _ _ _)))
      (Nat.cast_nonneg _)
  linarith

/-- The iterated recurrence with exact normalizers, before applying Mertens. -/
theorem truncatedMoment_le_recursionError (w : MultiplicativeWeight) (δ T : ℝ) (θ : ℕ → ℝ)
    {q : ℕ} (hq : 1 ≤ q) (x : ℝ) :
    truncatedMoment w δ T θ q x ≤ recursionError w δ T θ q x / normalizer w x +
      ∑ p ∈ primesLT x, w p * recursionError w δ T θ q p / ((p : ℝ) * normalizer w p) := by
  let V := recursionError w δ T θ q
  have h := prime_recursion_le w (fun y ↦ normalizer w y * truncatedMoment w δ T θ q y) V
    (fun y ↦ by simpa only [mul_assoc] using truncatedMoment_largest_prime_le w δ T θ hq y) x
  have hbound : normalizer w x * truncatedMoment w δ T θ q x ≤
      V x + ∑ p ∈ primesLT x, (w p * V p / p) * (normalizer w x / normalizer w p) := by
    refine h.trans (add_le_add le_rfl (sum_le_sum (fun p hp ↦ ?_)))
    exact mul_le_mul_of_nonneg_left (prime_tail_product_le w (mem_primesLT.1 hp).2.le)
      (div_nonneg (mul_nonneg (w.nonneg p) (recursionError_pos w δ T θ q p).le) (Nat.cast_nonneg p))
  have hh : truncatedMoment w δ T θ q x ≤
      (V x + ∑ p ∈ primesLT x, (w p * V p / p) * (normalizer w x / normalizer w p)) / normalizer w x :=
    (le_div_iff₀ (normalizer_pos w x)).2 (by simpa only [mul_comm] using hbound)
  convert hh using 1
  rw [add_div, sum_div]
  congr 1
  apply sum_congr rfl
  intro p _
  dsimp only [V]
  field_simp [(normalizer_pos w x).ne']

/-- Equation (2.15): the iterated largest-prime bound, with one constant depending on the prime estimates, uniform in the moment order, penalty and threshold data. -/
theorem truncatedMoment_recursion_bound (w : MultiplicativeWeight) (hpw : PrimeEstimates w) : ∃ C > 0, ∀ δ T (θ : ℕ → ℝ) (q : ℕ) (x : ℝ),
    1 ≤ q → 2 ≤ x →
    truncatedMoment w δ T θ q x ≤ C * (recursionError w δ T θ q x / log x +
      ∑ p ∈ primesLT x, w p * recursionError w δ T θ q p / ((p : ℝ) * log p)) := by
  obtain ⟨c, _, hc, _, hnormal⟩ := hpw.normalizer_bounds
  refine ⟨c⁻¹, inv_pos.2 hc, fun δ T θ q x hq hx ↦ ?_⟩
  have hlog : ∀ y : ℝ, 2 ≤ y → 0 < log y := fun y hy ↦ log_pos (by linarith)
  have hV : ∀ y : ℝ, 2 ≤ y →
      recursionError w δ T θ q y / normalizer w y ≤ c⁻¹ * (recursionError w δ T θ q y / log y) := by
    intro y hy
    calc
      _ ≤ recursionError w δ T θ q y / (c * log y) :=
        div_le_div_of_nonneg_left (recursionError_pos w δ T θ q y).le
          (mul_pos hc (hlog y hy)) (hnormal y hy).1
      _ = _ := by ring
  calc
    _ ≤ recursionError w δ T θ q x / normalizer w x +
        ∑ p ∈ primesLT x, w p * recursionError w δ T θ q p / ((p : ℝ) * normalizer w p) :=
      truncatedMoment_le_recursionError w δ T θ hq x
    _ ≤ c⁻¹ * (recursionError w δ T θ q x / log x) +
        ∑ p ∈ primesLT x, c⁻¹ * (w p * recursionError w δ T θ q p / ((p : ℝ) * log p)) := by
      apply add_le_add (hV x hx)
      apply sum_le_sum
      intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_primesLT.1 hp).1.two_le
      have h := div_le_div_of_nonneg_right (hV p hp2) (Nat.cast_nonneg p)
      have hw := mul_le_mul_of_nonneg_left h (w.nonneg p)
      convert hw using 1 <;> ring
    _ = _ := by rw [← mul_sum, ← mul_add]


/-- Bounded prime weights can be absorbed in the recurrence constant. -/
theorem truncatedMoment_recursion_bound_unweighted (w : MultiplicativeWeight)
    (hpw : PrimeEstimates w) : ∃ C > 0, ∀ δ T (θ : ℕ → ℝ) (q : ℕ) (x : ℝ),
    1 ≤ q → 2 ≤ x →
    truncatedMoment w δ T θ q x ≤ C * (recursionError w δ T θ q x / log x +
      ∑ p ∈ primesLT x, recursionError w δ T θ q p / ((p : ℝ) * log p)) := by
  obtain ⟨C, hC, hrec⟩ := truncatedMoment_recursion_bound w hpw
  let A := hpw.primeBound + 1
  have hA : 0 < A := by dsimp [A]; linarith [hpw.primeBound_nonneg]
  refine ⟨C * A, mul_pos hC hA, fun δ T θ q x hq hx ↦ ?_⟩
  have hxlog : 0 < log x := log_pos (by linarith)
  have hfirst : recursionError w δ T θ q x / log x ≤
      A * (recursionError w δ T θ q x / log x) := by
    have h0 := div_nonneg (recursionError_pos w δ T θ q x).le hxlog.le
    have h1 : 1 ≤ A := by dsimp [A]; linarith [hpw.primeBound_nonneg]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right h1 h0
  have hsum : (∑ p ∈ primesLT x, w p * recursionError w δ T θ q p / ((p : ℝ) * log p)) ≤
      A * ∑ p ∈ primesLT x, recursionError w δ T θ q p / ((p : ℝ) * log p) := by
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_primesLT.1 hp).1.two_le
    have hlog : 0 < log (p : ℝ) := log_pos (by linarith)
    have hwp : w p ≤ A := (hpw.prime_le p (mem_primesLT.1 hp).1).trans
      (by dsimp [A]; linarith)
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_right hwp
      (div_nonneg (recursionError_pos w δ T θ q p).le (by positivity : 0 ≤ (p : ℝ) * log p))
  have h := (hrec δ T θ q x hq hx).trans
    (mul_le_mul_of_nonneg_left (add_le_add hfirst hsum) hC.le)
  convert h using 1; ring

end BretecheTenenbaumMean.WeightedModel
