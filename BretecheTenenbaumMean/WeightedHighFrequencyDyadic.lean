module

public import BretecheTenenbaumMean.WeightedDyadicGoodSets
public import BretecheTenenbaumMean.WeightedHighFrequencyPrimeBound
public import BretecheTenenbaumMean.WeightedPrimeConsequences
public import BretecheTenenbaumMean.HighFrequencyDyadic

@[expose] public section

/-! # Weighted high-frequency estimates on the dyadic good-set layers -/

namespace BretecheTenenbaumMean.WeightedModel

open Real Finset PrimeSums

theorem high_frequency_dyadic_bound (w : MultiplicativeWeight) (hp : PrimeEstimates w) : ∃ C > 0, ∀ δ T x θ φ (j : ℕ),
    0 < T → 0 < θ → θ ≤ φ → φ ≤ 1 → exp θ⁻¹ ≤ x →
    expectation w x ((dyadicGoodSet δ T (exp φ⁻¹) j).indicator
      (fun n ↦ normalizedPolynomial n θ * normalizedPolynomial n φ)) ≤
      C * (sqrt (goodEnvelope δ T (exp φ⁻¹) * goodEnvelope δ T (exp θ⁻¹)) /
        sqrt ((2 : ℝ) ^ j)) *
      ((φ / θ) ^ sqrt 2 * (1 + θ * log x) *
        sqrt (φ * log x / (1 + (φ - θ) * log x)) /
        (φ ^ 2 * sqrt (log (3 / φ)) * log x)) := by
  obtain ⟨C, hC, hbound⟩ := high_frequency_layer_bound w hp
  obtain ⟨c, _, hc, _, hnorm⟩ := hp.normalizer_bounds
  refine ⟨C / c, div_pos hC hc, fun δ T x θ φ j hT hθ hθφ hφ1 hx ↦ ?_⟩
  have hφ := hθ.trans_le hθφ
  have hθ1 := hθφ.trans hφ1
  have ha : 1 ≤ exp φ⁻¹ := one_le_exp_iff.2 (inv_nonneg.2 hφ.le)
  have hb : 1 ≤ exp θ⁻¹ := one_le_exp_iff.2 (inv_nonneg.2 hθ.le)
  have hx2 := (two_le_exp_inv hθ hθ1).trans hx
  have hl : 0 < log x := log_pos (by linarith)
  obtain ⟨r, hr⟩ := dyadicGoodSet_expectation_le_layer w
    (x := x) (θ := θ) (φ := φ) j hT ha hb
  refine hr.trans ?_
  have hs : 0 ≤ (∑ n ∈ smoothSupport x,
      if (smallPrimePart n (exp φ⁻¹)).primeFactors.card = r
      then w n * twoFrequencyWeight n (exp φ⁻¹) (exp θ⁻¹) θ φ / n else 0) := by
    apply sum_nonneg
    intro n _
    split_ifs
    · exact div_nonneg (mul_nonneg (w.nonneg n) (twoFrequencyWeight_nonneg n _ _ _ _)) (Nat.cast_nonneg n)
    · rfl
  have hdiv := div_le_div₀ (hs.trans (hbound x θ φ r hθ hθφ hφ1 hx))
    (hbound x θ φ r hθ hθφ hφ1 hx)
    (mul_pos hc hl) (hnorm x hx2).1
  have hmul := mul_le_mul_of_nonneg_left hdiv
    (show 0 ≤ sqrt (goodEnvelope δ T (exp φ⁻¹) * goodEnvelope δ T (exp θ⁻¹)) /
      sqrt ((2 : ℝ) ^ j) from div_nonneg (sqrt_nonneg _) (sqrt_nonneg _))
  convert hmul using 1; ring


theorem high_frequency_dyadic_penalty_bound (w : MultiplicativeWeight) (hp : PrimeEstimates w) : ∃ C > 0, ∀ δ T x θ φ (j : ℕ),
    0 < T → 0 < θ → θ ≤ φ → φ ≤ 1 → exp θ⁻¹ ≤ x →
    expectation w x ((dyadicGoodSet δ T (exp φ⁻¹) j).indicator
      (fun n ↦ normalizedPolynomial n θ * normalizedPolynomial n φ)) ≤
      C * T * exp (-(penalty δ T (exp θ⁻¹) + penalty δ T (exp φ⁻¹)) / 2) /
        sqrt ((2 : ℝ) ^ j) *
      ((φ / θ) ^ sqrt 2 * (1 + θ * log x) *
        sqrt (φ * log x / (1 + (φ - θ) * log x)) /
        (sqrt (θ * φ) * φ ^ 2 * sqrt (log (3 / φ)) * log x)) := by
  obtain ⟨C, hC, hbound⟩ := high_frequency_dyadic_bound w hp
  refine ⟨4 * C, by positivity, fun δ T x θ φ j hT hθ hθφ hφ1 hx ↦ ?_⟩
  have hφ := hθ.trans_le hθφ
  have hl : 0 < log x := log_pos (by
    have := (two_le_exp_inv hθ (hθφ.trans hφ1)).trans hx; linarith)
  have hlog : 0 < log (3 / φ) := log_pos ((lt_div_iff₀ hφ).2 (by linarith))
  have hcoef := div_le_div_of_nonneg_right
    (frequency_sqrt_envelope_le (δ := δ) hT.le hθ (hθφ.trans hφ1) hφ hφ1)
    (sqrt_nonneg ((2 : ℝ) ^ j))
  refine (hbound δ T x θ φ j hT hθ hθφ hφ1 hx).trans ?_
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef hC.le)
    (show 0 ≤ (φ / θ) ^ sqrt 2 * (1 + θ * log x) *
      sqrt (φ * log x / (1 + (φ - θ) * log x)) /
      (φ ^ 2 * sqrt (log (3 / φ)) * log x) by positivity)
  convert hm using 1; ring


theorem high_frequency_goodSet_bound (w : MultiplicativeWeight) (hp : PrimeEstimates w) : ∃ C > 0, ∀ δ T x θ φ,
    0 < T → 0 < θ → θ ≤ φ → φ ≤ 1 → exp θ⁻¹ ≤ x →
    expectation w x ((goodSet δ T).indicator
      (fun n ↦ normalizedPolynomial n θ * normalizedPolynomial n φ)) ≤
      C * T * exp (-(penalty δ T (exp θ⁻¹) + penalty δ T (exp φ⁻¹)) / 2) *
        highFrequencyKernel x θ φ := by
  obtain ⟨C, hC, hbound⟩ := high_frequency_dyadic_penalty_bound w hp
  refine ⟨4 * C, by positivity, fun δ T x θ φ hT hθ hθφ hφ1 hx ↦ ?_⟩
  have hφ := hθ.trans_le hθφ
  have hx1 : 1 ≤ x := (one_le_exp_iff.2 (inv_nonneg.2 hθ.le)).trans hx
  have hy : 1 ≤ exp φ⁻¹ := one_le_exp_iff.2 (inv_nonneg.2 hφ.le)
  have hk := highFrequencyKernel_nonneg hx1 hθ.le hφ.le
  let A := C * T * exp (-(penalty δ T (exp θ⁻¹) + penalty δ T (exp φ⁻¹)) / 2) *
    highFrequencyKernel x θ φ
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have h := goodSet_expectation_le_of_dyadic w (δ := δ) (T := T) (x := x) hy hA
    (fun n ↦ normalizedPolynomial n θ * normalizedPolynomial n φ) (fun j ↦ ?_)
  · convert h using 1
    dsimp only [A]
    ring
  · convert hbound δ T x θ φ j hT hθ hθφ hφ1 hx using 1
    dsimp only [A, highFrequencyKernel]
    ring


end BretecheTenenbaumMean.WeightedModel
