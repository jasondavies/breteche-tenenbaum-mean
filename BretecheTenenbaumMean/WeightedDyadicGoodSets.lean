module

public import BretecheTenenbaumMean.DyadicGoodSets
public import BretecheTenenbaumMean.WeightedProbability

@[expose] public section

/-! # Weighted expectations of the dyadic good-set partition -/

namespace BretecheTenenbaumMean.WeightedModel

open Real Finset

theorem dyadicGoodSet_expectation_le_layer (w : MultiplicativeWeight) {δ T x a b θ φ : ℝ} (j : ℕ)
    (hT : 0 < T) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∃ r : ℕ,
      expectation w x ((dyadicGoodSet δ T a j).indicator
        (fun n ↦ normalizedPolynomial n θ * normalizedPolynomial n φ)) ≤
      (sqrt (goodEnvelope δ T a * goodEnvelope δ T b) / sqrt ((2 : ℝ) ^ j)) *
        ((∑ n ∈ smoothSupport x, if (smallPrimePart n a).primeFactors.card = r
          then w n * twoFrequencyWeight n a b θ φ / n else 0) / normalizer w x) := by
  classical
  obtain ⟨r, hr⟩ := dyadicGoodSet_fixed_prime_count δ T a j
  refine ⟨r, ?_⟩
  let A := sqrt (goodEnvelope δ T a * goodEnvelope δ T b) / sqrt ((2 : ℝ) ^ j)
  have hA : 0 ≤ A := div_nonneg (sqrt_nonneg _) (sqrt_nonneg _)
  calc _ ≤ expectation w x (fun n ↦ A *
      (if (smallPrimePart n a).primeFactors.card = r then twoFrequencyWeight n a b θ φ else 0)) := by
        apply expectation_mono
        intro n _
        by_cases hn : n ∈ dyadicGoodSet δ T a j
        · rw [Set.indicator_of_mem hn, ite_eq_left (hr n hn),
            normalizedPolynomial_mul_eq_twoFrequencyWeight n a b θ φ]
          exact mul_le_mul_of_nonneg_right (dyadicGoodSet_sqrt_tau_le hT ha hb hn)
            (twoFrequencyWeight_nonneg n a b θ φ)
        · rw [Set.indicator_of_notMem hn]
          exact mul_nonneg hA (by split_ifs; exact twoFrequencyWeight_nonneg n a b θ φ; rfl)
    _ = _ := by
      rw [expectation_const_mul]
      simp only [expectation, mul_ite, mul_zero, ite_div, zero_div]
      rfl


theorem goodSet_expectation_eq_dyadic_sum (w : MultiplicativeWeight) {δ T y : ℝ} (hy : 1 ≤ y) {N : ℕ}
    (hN : ∀ n j, n ∈ dyadicGoodSet δ T y j → j < N) (x : ℝ) (f : ℕ → ℝ) :
    expectation w x ((goodSet δ T).indicator f) =
      ∑ j ∈ range N, expectation w x ((dyadicGoodSet δ T y j).indicator f) := by
  classical
  unfold expectation
  simp_rw [goodSet_indicator_eq_dyadic_sum hy hN f, mul_sum, sum_div]
  rw [sum_comm]


theorem goodSet_expectation_le_of_dyadic (w : MultiplicativeWeight) {δ T y x A : ℝ} (hy : 1 ≤ y)
    (hA : 0 ≤ A) (f : ℕ → ℝ)
    (hbound : ∀ j, expectation w x ((dyadicGoodSet δ T y j).indicator f) ≤
      A / sqrt ((2 : ℝ) ^ j)) :
    expectation w x ((goodSet δ T).indicator f) ≤ 4 * A := by
  obtain ⟨N, hN⟩ := exists_dyadicGoodSet_cutoff δ T y
  rw [goodSet_expectation_eq_dyadic_sum w hy hN]
  calc _ ≤ ∑ j ∈ range N, A / sqrt ((2 : ℝ) ^ j) := sum_le_sum (fun j _ ↦ hbound j)
    _ = A * ∑ j ∈ range N, (sqrt ((2 : ℝ) ^ j))⁻¹ := by simp_rw [div_eq_mul_inv]; rw [mul_sum]
    _ ≤ A * 4 := mul_le_mul_of_nonneg_left (sum_inv_sqrt_two_pow_le N) hA
    _ = _ := by ring


end BretecheTenenbaumMean.WeightedModel
