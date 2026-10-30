module

public import BretecheTenenbaumMean.WeightedSmallPrimeFrequency
public import BretecheTenenbaumMean.WeightedEventBounds
public import BretecheTenenbaumMean.IntermediateFrequency
public import BretecheTenenbaumMean.Penalty

@[expose] public section

/-! # The weighted intermediate-frequency contribution

The integration starts at zero, giving an upper bound for the paper's interval
starting at `1/log x`. The singular power majorant is integrable for `δ > 0`.
-/

namespace BretecheTenenbaumMean.WeightedModel

open Real Finset MeasureTheory

/-- Restricting the finite expectation to any fixed set preserves continuity
in the frequency. -/
theorem continuous_expectation_indicator_normalizedPolynomial (w : MultiplicativeWeight) (x : ℝ) (E : Set ℕ) :
    Continuous (fun θ ↦ expectation w x (E.indicator (fun n ↦ normalizedPolynomial n θ))) := by
  classical
  unfold expectation
  apply Continuous.div_const
  apply continuous_finsetSum
  intro n _
  by_cases hn : n ∈ E
  · simp only [Set.indicator_of_mem hn]
    exact (((((continuous_divisorPolynomial n).norm.pow 2).div_const (tau n)).const_mul (w n)).div_const (n : ℝ))
  · simp only [Set.indicator_of_notMem hn, mul_zero, zero_div]
    exact continuous_const

/-- An explicit exponent works for the intermediate-frequency mean. -/
theorem intermediate_frequency_mean_bound (w : MultiplicativeWeight) (hp : PrimeEstimates w) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ C > 0, ∀ x T, 2 ≤ x → 3 ≤ T →
    (∫ θ in (0 : ℝ)..T ^ (-(16 + δ⁻¹)),
      expectation w x ((goodSet δ T).indicator (fun n ↦ normalizedPolynomial n θ))) ≤ C := by
  obtain ⟨C, hC, h⟩ := goodSet_frequency_bound w hp
  refine ⟨C * (4 : ℝ) ^ (1 - δ) / δ, div_pos (mul_pos hC (rpow_pos_of_pos (by norm_num) _)) hδ,
    fun x T hx hT ↦ ?_⟩
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  let K := 16 + δ⁻¹
  let b := T ^ (-K)
  have hK16 : 16 ≤ K := by
    dsimp only [K]
    have := inv_nonneg.2 hδ.le
    linarith
  have hKδ : 1 ≤ K * δ := by
    dsimp only [K]
    rw [add_mul, inv_mul_cancel₀ hδ.ne']
    nlinarith
  have hb : 0 < b := rpow_pos_of_pos hT0 _
  have hb1 : b ≤ 1 := by
    calc b ≤ T ^ (0 : ℝ) := rpow_le_rpow_of_exponent_le hT1 (by linarith)
         _ = 1 := rpow_zero _
  have hbsmall : b ≤ T ^ (-16 : ℝ) := rpow_le_rpow_of_exponent_le hT1 (by linarith)
  have hpow : T ^ (1 - δ) * b ^ δ ≤ 1 := by
    dsimp only [b]
    rw [← rpow_mul hT0.le, ← rpow_add hT0]
    calc _ ≤ T ^ (0 : ℝ) := rpow_le_rpow_of_exponent_le hT1 (by nlinarith)
         _ = 1 := rpow_zero _
  have hi : IntervalIntegrable (fun θ : ℝ ↦ θ ^ (δ - 1)) volume 0 b :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hbound : (∫ θ in (0 : ℝ)..b,
      expectation w x ((goodSet δ T).indicator (fun n ↦ normalizedPolynomial n θ))) ≤
      ∫ θ in (0 : ℝ)..b, (C * (4 : ℝ) ^ (1 - δ) * T ^ (1 - δ)) * θ ^ (δ - 1) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hb.le
      ((continuous_expectation_indicator_normalizedPolynomial w x (goodSet δ T)).intervalIntegrable _ _)
      (hi.const_mul _)
    intro θ hθ
    have hθ1 : θ ≤ 1 := hθ.2.le.trans hb1
    have hsmall : θ ≤ T ^ (-16 : ℝ) := hθ.2.le.trans hbsmall
    have hp := frequency_penalty_envelope_le hδ1 (by linarith : 1 < T) hθ.1 hθ1 hsmall
    calc _ ≤ C * T * log (3 * exp θ⁻¹) * exp (-penalty δ T (exp θ⁻¹)) :=
            h δ T x θ hT0.le hx hθ.1 hθ1
         _ = C * (T * log (3 * exp θ⁻¹) * exp (-penalty δ T (exp θ⁻¹))) := by ring
         _ ≤ C * ((4 : ℝ) ^ (1 - δ) * T ^ (1 - δ) * θ ^ (δ - 1)) :=
            mul_le_mul_of_nonneg_left hp hC.le
         _ = _ := by ring
  have hint : (∫ θ in (0 : ℝ)..b, θ ^ (δ - 1)) = b ^ δ / δ := by
    rw [integral_rpow (Or.inl (by linarith))]
    simp only [sub_add_cancel, zero_rpow hδ.ne', sub_zero]
  change (∫ θ in (0 : ℝ)..b, _) ≤ _
  refine hbound.trans ?_
  rw [intervalIntegral.integral_const_mul, hint]
  calc (C * (4 : ℝ) ^ (1 - δ) * T ^ (1 - δ)) * (b ^ δ / δ)
      = (C * (4 : ℝ) ^ (1 - δ) / δ) * (T ^ (1 - δ) * b ^ δ) := by ring
    _ ≤ (C * (4 : ℝ) ^ (1 - δ) / δ) * 1 :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := mul_one _

/-- Finite expectation commutes with the frequency integral after restriction
to a fixed arithmetic set. -/
theorem expectation_indicator_frequencyIntegral (w : MultiplicativeWeight) (x a b : ℝ) (E : Set ℕ) :
    expectation w x (E.indicator (fun n ↦ frequencyIntegral n a b)) =
      ∫ θ in a..b, expectation w x (E.indicator (fun n ↦ normalizedPolynomial n θ)) := by
  classical
  rw [integral_expectation w x a b (fun n θ ↦ E.indicator (fun m ↦ normalizedPolynomial m θ) n)]
  · congr 1
    ext n
    by_cases hn : n ∈ E
    · simp only [Set.indicator_of_mem hn, frequencyIntegral]
    · simp only [Set.indicator_of_notMem hn, intervalIntegral.integral_zero]
  · intro n _
    by_cases hn : n ∈ E
    · simpa only [Set.indicator_of_mem hn] using intervalIntegrable_normalizedPolynomial n a b
    · simp only [Set.indicator_of_notMem hn]
      exact intervalIntegrable_const

/-- The intermediate-frequency exceptional probability is `Oδ(1/R)`.
Taking `a = 1/log x` and `R = c T` gives the estimate for `α` in §2.2. -/
theorem intermediate_frequency_probability_bound (w : MultiplicativeWeight) (hp : PrimeEstimates w) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ C > 0, ∀ x T a R, 2 ≤ x → 3 ≤ T → 0 ≤ a → a ≤ T ^ (-(16 + δ⁻¹)) → 0 < R →
    probability w x {n | n ∈ goodSet δ T ∧ R < frequencyIntegral n a (T ^ (-(16 + δ⁻¹)))} ≤
      C / R := by
  classical
  obtain ⟨C, hC, h⟩ := intermediate_frequency_mean_bound w hp hδ hδ1
  refine ⟨C, hC, fun x T a R hx hT ha hab hR ↦ ?_⟩
  let b := T ^ (-(16 + δ⁻¹))
  let f := (goodSet δ T).indicator (fun n ↦ frequencyIntegral n a b)
  have hf : ∀ n ∈ smoothSupport x, 0 ≤ f n := by
    intro n _
    exact Set.indicator_nonneg (fun m _ ↦ frequencyIntegral_nonneg m hab) n
  have he : {n | n ∈ goodSet δ T ∧ R < frequencyIntegral n a b} = {n | R < f n} := by
    ext n
    by_cases hn : n ∈ goodSet δ T
    · simp only [Set.mem_ofPred_eq, hn, true_and, f, Set.indicator_of_mem hn]
    · simp only [Set.mem_ofPred_eq, hn, false_and, f, Set.indicator_of_notMem hn,
        not_lt.mpr hR.le]
  have hmean : expectation w x f ≤ C := by
    calc expectation w x f ≤ expectation w x ((goodSet δ T).indicator (fun n ↦ frequencyIntegral n 0 b)) := by
            apply expectation_mono
            intro n _
            by_cases hn : n ∈ goodSet δ T
            · simp only [f, Set.indicator_of_mem hn]
              exact frequencyIntegral_mono_interval n ha hab le_rfl
            · simp only [f, Set.indicator_of_notMem hn, le_refl]
         _ = ∫ θ in (0 : ℝ)..b, expectation w x ((goodSet δ T).indicator
              (fun n ↦ normalizedPolynomial n θ)) := expectation_indicator_frequencyIntegral _ _ _ _ _
         _ ≤ C := h x T hx hT
  change probability w x {n | n ∈ goodSet δ T ∧ R < frequencyIntegral n a b} ≤ C / R
  rw [he]
  exact (probability_gt_le w x _ hf hR).trans (div_le_div_of_nonneg_right hmean hR.le)

end BretecheTenenbaumMean.WeightedModel
