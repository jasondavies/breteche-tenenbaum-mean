module

public import BretecheTenenbaumMean.WeightedHighFrequencyDyadic
public import BretecheTenenbaumMean.HighFrequencyIntegration

@[expose] public section

/-! # Integration of the weighted two-frequency expectation -/

namespace BretecheTenenbaumMean.WeightedModel

open Real MeasureTheory

theorem high_frequency_goodSet_one_penalty_bound (w : MultiplicativeWeight) (hprime : PrimeEstimates w) : ∃ C > 0, ∀ δ T x θ φ,
    0 ≤ δ → 1 ≤ T → 0 < θ → θ ≤ φ → φ ≤ 1 → exp θ⁻¹ ≤ x →
    expectation w x ((goodSet δ T).indicator
      (fun n ↦ normalizedPolynomial n θ * normalizedPolynomial n φ)) ≤
      C * T * exp (-penalty δ T (exp θ⁻¹) / 2) *
        regularizedHighKernel (log x)⁻¹ θ φ := by
  obtain ⟨C, hC, hbound⟩ := high_frequency_goodSet_bound w hprime
  refine ⟨C, hC, fun δ T x θ φ hδ hT hθ hθφ hφ1 hx ↦ ?_⟩
  have hT0 : 0 < T := by linarith
  have hφ : 0 < φ := hθ.trans_le hθφ
  have hx1 : 1 < x := (one_lt_exp_iff.2 (inv_pos.2 hθ)).trans_le hx
  have hp := penalty_nonneg hδ hT (one_le_exp_iff.2 (inv_nonneg.2 hφ.le))
  have he : exp (-(penalty δ T (exp θ⁻¹) + penalty δ T (exp φ⁻¹)) / 2) ≤
      exp (-penalty δ T (exp θ⁻¹) / 2) := exp_le_exp.2 (by linarith)
  rw [← highFrequencyKernel_eq_regularized hx1 hθ hθφ]
  exact (hbound δ T x θ φ hT0 hθ hθφ hφ1 hx).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (mul_pos hC hT0).le)
      (highFrequencyKernel_nonneg hx1.le hθ.le hφ.le))


theorem continuous_expectation_indicator_twoFrequency (w : MultiplicativeWeight) (x θ : ℝ) (E : Set ℕ) :
    Continuous (fun φ ↦ expectation w x (E.indicator
      (fun n ↦ normalizedPolynomial n θ * normalizedPolynomial n φ))) := by
  classical
  unfold expectation
  apply Continuous.div_const
  apply continuous_finsetSum
  intro n _
  by_cases hn : n ∈ E
  · simp only [Set.indicator_of_mem hn]
    exact ((((((continuous_divisorPolynomial n).norm.pow 2).div_const (tau n)).const_mul
      (normalizedPolynomial n θ)).const_mul (w n)).div_const (n : ℝ))
  · simp only [Set.indicator_of_notMem hn, mul_zero, zero_div]
    exact continuous_const

/-- The larger-frequency integral of the good-set expectation, with the
smaller-frequency penalty retained for the final integration. -/
theorem high_frequency_goodSet_inner_integral (w : MultiplicativeWeight) (hprime : PrimeEstimates w) : ∃ C > 0, ∀ δ T x θ,
    0 ≤ δ → 1 ≤ T → 0 < θ → θ ≤ 1 → exp θ⁻¹ ≤ x →
    (∫ φ in θ..1, expectation w x ((goodSet δ T).indicator
      (fun n ↦ normalizedPolynomial n θ * normalizedPolynomial n φ))) ≤
      C * T * exp (-penalty δ T (exp θ⁻¹) / 2) / (θ * sqrt (log (3 / θ))) := by
  obtain ⟨C, hC, hbound⟩ := high_frequency_goodSet_one_penalty_bound w hprime
  refine ⟨816 * C, by positivity, fun δ T x θ hδ hT hθ hθ1 hx ↦ ?_⟩
  have hε := inv_log_le_frequency hθ hx
  let A := C * T * exp (-penalty δ T (exp θ⁻¹) / 2)
  have hA : 0 ≤ A := by
    have : 0 < T := by linarith
    dsimp only [A]
    positivity
  have hi := (continuous_expectation_indicator_twoFrequency w x θ (goodSet δ T)).intervalIntegrable (μ := volume) θ 1
  have hk := (continuousOn_regularizedHighKernel hε.1 hθ (b := 1) le_rfl).intervalIntegrable_of_Icc (μ := volume) hθ1
  have hm := intervalIntegral.integral_mono_on hθ1 hi (hk.const_mul A)
    (fun φ hφ ↦ hbound δ T x θ φ hδ hT hθ hφ.1 hφ.2 hx)
  rw [intervalIntegral.integral_const_mul] at hm
  calc _ ≤ A * (∫ φ in θ..1, regularizedHighKernel (log x)⁻¹ θ φ) := hm
    _ ≤ A * (816 / (θ * sqrt (log (3 / θ)))) :=
      mul_le_mul_of_nonneg_left (integral_regularizedHighKernel_le hε.1 hε.2 hθ hθ1) hA
    _ = _ := by dsimp only [A]; ring


end BretecheTenenbaumMean.WeightedModel
