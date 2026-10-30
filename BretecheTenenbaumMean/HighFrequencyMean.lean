module

public import BretecheTenenbaumMean.HighFrequencyIntegration
public import BretecheTenenbaumMean.PenaltyIntegral
public import BretecheTenenbaumMean.FrequencyAverage

@[expose] public section

/-! # The high-frequency second moment -/

namespace BretecheTenenbaumMean

open Real MeasureTheory

/-- A continuous integrand has a continuous integral with variable lower endpoint. -/
theorem continuous_tail_integral {f : ℝ → ℝ} (hf : Continuous f) (b : ℝ) :
    Continuous (fun θ ↦ ∫ φ in θ..b, f φ) := by
  have hc : Continuous (fun θ ↦ ∫ φ in b..θ, f φ) :=
    continuous_iff_continuousAt.2 (fun θ ↦ (hf.integral_hasStrictDerivAt b θ).hasDerivAt.continuousAt)
  convert hc.neg using 1
  funext θ
  exact intervalIntegral.integral_symm b θ

/-- Integrate one frequency before averaging over the finite probability space. -/
theorem integral_twoFrequency_expectation (x θ b : ℝ) (E : Set ℕ) :
    (∫ φ in θ..b, expectation x (E.indicator
      (fun n ↦ normalizedPolynomial n θ * normalizedPolynomial n φ))) =
    expectation x (E.indicator
      (fun n ↦ normalizedPolynomial n θ * ∫ φ in θ..b, normalizedPolynomial n φ)) := by
  classical
  have hi (n : ℕ) : IntervalIntegrable (normalizedPolynomial n) volume θ b :=
    (((continuous_divisorPolynomial n).norm.pow 2).div_const (tau n)).intervalIntegrable _ _
  rw [integral_expectation x θ b (fun n φ ↦ E.indicator
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

/-- Continuity of the inner integral, including its varying lower endpoint. -/
theorem continuous_twoFrequency_inner (x b : ℝ) (E : Set ℕ) :
    Continuous (fun θ ↦ ∫ φ in θ..b, expectation x (E.indicator
      (fun n ↦ normalizedPolynomial n θ * normalizedPolynomial n φ))) := by
  classical
  simp_rw [integral_twoFrequency_expectation]
  unfold expectation
  apply Continuous.div_const
  apply continuous_finsetSum
  intro n _
  by_cases hn : n ∈ E
  · simp only [Set.indicator_of_mem hn]
    have hc : Continuous (normalizedPolynomial n) :=
      ((continuous_divisorPolynomial n).norm.pow 2).div_const (tau n)
    exact (hc.mul (continuous_tail_integral hc b)).div_const (n : ℝ)
  · simp only [Set.indicator_of_notMem hn, zero_div]
    exact continuous_const

/-- The two-variable high-frequency integral is `O(T)` on every admissible
ordered triangle. No relation between `T` and `log x` is required. -/
theorem high_frequency_triangle_bound {δ : ℝ} (hδ : 0 < δ) : ∃ C > 0, ∀ T x a,
    1 < T → 0 < a → a ≤ 1 → exp a⁻¹ ≤ x →
    (∫ θ in a..1, ∫ φ in θ..1, expectation x ((goodSet δ T).indicator
      (fun n ↦ normalizedPolynomial n θ * normalizedPolynomial n φ))) ≤ C * T := by
  obtain ⟨C, hC, hinner⟩ := high_frequency_goodSet_inner_integral
  let B := 6 * (sqrt (π / (δ / 2)) + sqrt (π / (δ * criticalSlope / 2)))
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨C * B, mul_pos hC hB, fun T x a hT ha ha1 hx ↦ ?_⟩
  have hT0 : 0 < T := by linarith
  have hi := (continuous_twoFrequency_inner x 1 (goodSet δ T)).intervalIntegrable (μ := volume) a 1
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

/-- For a product integrand, the ordered triangle has exactly half the square's
integral. The proof uses the fundamental theorem of calculus. -/
theorem integral_product_triangle {f : ℝ → ℝ} (hf : Continuous f) (a b : ℝ) :
    (∫ θ in a..b, f θ * ∫ φ in θ..b, f φ) = (∫ θ in a..b, f θ) ^ 2 / 2 := by
  have hder : ∀ θ ∈ Set.uIcc a b,
      HasDerivAt (fun θ ↦ -(∫ φ in b..θ, f φ) ^ 2 / 2)
        (f θ * ∫ φ in θ..b, f φ) θ := by
    intro θ _
    have h := ((hf.integral_hasStrictDerivAt b θ).hasDerivAt.pow 2).neg.div_const 2
    convert h using 1
    rw [intervalIntegral.integral_symm b θ]
    ring
  have hi := (hf.mul (continuous_tail_integral hf b)).intervalIntegrable (μ := volume) a b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hi]
  simp only [intervalIntegral.integral_same, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, neg_zero, zero_div, zero_sub, neg_div, neg_neg]
  rw [intervalIntegral.integral_symm a b]
  ring

/-- Exact identity between the averaged squared frequency integral and twice
the ordered two-frequency integral. -/
theorem expectation_frequency_integral_sq (x a b : ℝ) (E : Set ℕ) :
    expectation x (E.indicator (fun n ↦ (∫ θ in a..b, normalizedPolynomial n θ) ^ 2)) =
      2 * (∫ θ in a..b, ∫ φ in θ..b, expectation x (E.indicator
        (fun n ↦ normalizedPolynomial n θ * normalizedPolynomial n φ))) := by
  classical
  simp_rw [integral_twoFrequency_expectation]
  have hc (n : ℕ) : Continuous (normalizedPolynomial n) :=
    ((continuous_divisorPolynomial n).norm.pow 2).div_const (tau n)
  rw [integral_expectation x a b (fun n θ ↦ E.indicator
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

/-- The high-frequency second-moment estimate used in Proposition 2.1. -/
theorem high_frequency_second_moment_bound {δ : ℝ} (hδ : 0 < δ) : ∃ C > 0, ∀ T x a,
    1 < T → 0 < a → a ≤ 1 → exp a⁻¹ ≤ x →
    expectation x ((goodSet δ T).indicator
      (fun n ↦ (∫ θ in a..1, normalizedPolynomial n θ) ^ 2)) ≤ C * T := by
  obtain ⟨C, hC, hbound⟩ := high_frequency_triangle_bound hδ
  refine ⟨2 * C, by positivity, fun T x a hT ha ha1 hx ↦ ?_⟩
  rw [expectation_frequency_integral_sq]
  have h := mul_le_mul_of_nonneg_left (hbound T x a hT ha ha1 hx) (by norm_num : (0 : ℝ) ≤ 2)
  convert h using 1
  ring

end BretecheTenenbaumMean
