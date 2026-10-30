module

public import BretecheTenenbaumMean.WeightedHighFrequencyIntegration
public import BretecheTenenbaumMean.WeightedFrequency
public import BretecheTenenbaumMean.HighFrequencyMean

@[expose] public section

/-! # The weighted high-frequency second moment -/

namespace BretecheTenenbaumMean.WeightedModel

open Real MeasureTheory

theorem integral_twoFrequency_expectation (w : MultiplicativeWeight) (x θ b : ℝ) (E : Set ℕ) :
    (∫ φ in θ..b, expectation w x (E.indicator
      (fun n ↦ normalizedPolynomial n θ * normalizedPolynomial n φ))) =
    expectation w x (E.indicator
      (fun n ↦ normalizedPolynomial n θ * ∫ φ in θ..b, normalizedPolynomial n φ)) := by
  classical
  have hi (n : ℕ) : IntervalIntegrable (normalizedPolynomial n) volume θ b :=
    (((continuous_divisorPolynomial n).norm.pow 2).div_const (tau n)).intervalIntegrable _ _
  rw [integral_expectation w x θ b (fun n φ ↦ E.indicator
    (fun n ↦ normalizedPolynomial n θ * normalizedPolynomial n φ) n)]
  · congr 1
    funext n
    by_cases hn : n ∈ E
    · simp only [Set.indicator_of_mem hn, intervalIntegral.integral_const_mul]
    · simp only [Set.indicator_of_notMem hn, intervalIntegral.integral_zero]
  · intro n _
    by_cases hn : n ∈ E
    · simpa only [Set.indicator_of_mem hn] using (hi n).const_mul (normalizedPolynomial n θ)
    · simpa only [Set.indicator_of_notMem hn] using (intervalIntegrable_const (c := (0 : ℝ)))


theorem continuous_twoFrequency_inner (w : MultiplicativeWeight) (x b : ℝ) (E : Set ℕ) :
    Continuous (fun θ ↦ ∫ φ in θ..b, expectation w x (E.indicator
      (fun n ↦ normalizedPolynomial n θ * normalizedPolynomial n φ))) := by
  classical
  simp_rw [integral_twoFrequency_expectation w]
  unfold expectation
  apply Continuous.div_const
  apply continuous_finsetSum
  intro n _
  by_cases hn : n ∈ E
  · simp only [Set.indicator_of_mem hn]
    have hc : Continuous (normalizedPolynomial n) :=
      ((continuous_divisorPolynomial n).norm.pow 2).div_const (tau n)
    exact ((hc.mul (continuous_tail_integral hc b)).const_mul (w n)).div_const (n : ℝ)
  · simp only [Set.indicator_of_notMem hn, mul_zero, zero_div]
    exact continuous_const


theorem high_frequency_triangle_bound (w : MultiplicativeWeight) (hp : PrimeEstimates w) {δ : ℝ} (hδ : 0 < δ) : ∃ C > 0, ∀ T x a,
    1 < T → 0 < a → a ≤ 1 → exp a⁻¹ ≤ x →
    (∫ θ in a..1, ∫ φ in θ..1, expectation w x ((goodSet δ T).indicator
      (fun n ↦ normalizedPolynomial n θ * normalizedPolynomial n φ))) ≤ C * T := by
  obtain ⟨C, hC, hinner⟩ := high_frequency_goodSet_inner_integral w hp
  let B := 6 * (sqrt (π / (δ / 2)) + sqrt (π / (δ * criticalSlope / 2)))
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨C * B, mul_pos hC hB, fun T x a hT ha ha1 hx ↦ ?_⟩
  have hT0 : 0 < T := by linarith
  have hi := (continuous_twoFrequency_inner w x 1 (goodSet δ T)).intervalIntegrable (μ := volume) a 1
  have hw := (continuousOn_frequencyPenaltyWeight (δ := δ) hT ha).intervalIntegrable_of_Icc (μ := volume) ha1
  have hm := intervalIntegral.integral_mono_on ha1 hi (hw.const_mul (C * T)) (fun θ hθ ↦ ?_)
  · rw [intervalIntegral.integral_const_mul] at hm
    calc _ ≤ (C * T) * (∫ θ in a..1, frequencyPenaltyWeight δ T θ) := hm
      _ ≤ (C * T) * B := mul_le_mul_of_nonneg_left
        (frequency_penalty_integral_le hδ hT ha ha1) (mul_pos hC hT0).le
      _ = _ := by ring
  · have hθ0 : 0 < θ := ha.trans_le hθ.1
    have hxθ : exp θ⁻¹ ≤ x := (exp_le_exp.2 (inv_anti₀ ha hθ.1)).trans hx
    convert hinner δ T x θ hδ.le hT.le hθ0 hθ.2 hxθ using 1
    unfold frequencyPenaltyWeight
    ring


theorem expectation_frequency_integral_sq (w : MultiplicativeWeight) (x a b : ℝ) (E : Set ℕ) :
    expectation w x (E.indicator (fun n ↦ (∫ θ in a..b, normalizedPolynomial n θ) ^ 2)) =
      2 * (∫ θ in a..b, ∫ φ in θ..b, expectation w x (E.indicator
        (fun n ↦ normalizedPolynomial n θ * normalizedPolynomial n φ))) := by
  classical
  simp_rw [integral_twoFrequency_expectation w]
  have hc (n : ℕ) : Continuous (normalizedPolynomial n) :=
    ((continuous_divisorPolynomial n).norm.pow 2).div_const (tau n)
  rw [integral_expectation w x a b (fun n θ ↦ E.indicator
    (fun n ↦ normalizedPolynomial n θ * ∫ φ in θ..b, normalizedPolynomial n φ) n)]
  · rw [← expectation_const_mul]
    congr 1
    funext n
    by_cases hn : n ∈ E
    · simp only [Set.indicator_of_mem hn, integral_product_triangle (hc n)]
      ring
    · simp only [Set.indicator_of_notMem hn, intervalIntegral.integral_zero, mul_zero]
  · intro n _
    by_cases hn : n ∈ E
    · simp only [Set.indicator_of_mem hn]
      convert ((hc n).mul (continuous_tail_integral (hc n) b)).intervalIntegrable (μ := volume) a b using 1
    · simpa only [Set.indicator_of_notMem hn] using (intervalIntegrable_const (c := (0 : ℝ)))


theorem high_frequency_second_moment_bound (w : MultiplicativeWeight) (hp : PrimeEstimates w) {δ : ℝ} (hδ : 0 < δ) : ∃ C > 0, ∀ T x a,
    1 < T → 0 < a → a ≤ 1 → exp a⁻¹ ≤ x →
    expectation w x ((goodSet δ T).indicator
      (fun n ↦ (∫ θ in a..1, normalizedPolynomial n θ) ^ 2)) ≤ C * T := by
  obtain ⟨C, hC, hbound⟩ := high_frequency_triangle_bound w hp hδ
  refine ⟨2 * C, by positivity, fun T x a hT ha ha1 hx ↦ ?_⟩
  rw [expectation_frequency_integral_sq w]
  have h := mul_le_mul_of_nonneg_left (hbound T x a hT ha ha1 hx) (by norm_num : (0 : ℝ) ≤ 2)
  convert h using 1
  ring


end BretecheTenenbaumMean.WeightedModel
