module

public import BretecheTenenbaumMean.PrimeSums.Abel

@[expose] public section

/-! # Oscillatory prime sums: comparison with a cosine integral

All estimates are uniform for frequencies of absolute value at most two,
including zero and sums or differences of frequencies in `[0,1]`.
-/

open Real Finset MeasureTheory intervalIntegral

namespace BretecheTenenbaumMean.PrimeSums

noncomputable def cosineWeight (ψ t : ℝ) : ℝ := cos (ψ * log t) * (t * log t)⁻¹

noncomputable def cosineWeightDeriv (ψ t : ℝ) : ℝ :=
  -(ψ * log t * sin (ψ * log t) + (log t + 1) * cos (ψ * log t)) / (t * log t) ^ 2

theorem hasDerivAt_cosineWeight (ψ : ℝ) {t : ℝ} (ht : 1 < t) :
    HasDerivAt (cosineWeight ψ) (cosineWeightDeriv ψ t) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl0 : log t ≠ 0 := (log_pos ht).ne'
  have h := (((hasDerivAt_log ht0).const_mul ψ).cos).mul (hasDerivAt_inv_mul_log ht)
  convert h using 1
  · rfl
  · dsimp only [cosineWeightDeriv]
    field_simp
    ring

theorem continuousOn_cosineWeightDeriv (ψ : ℝ) {x y : ℝ} (hx : 1 < x) :
    ContinuousOn (cosineWeightDeriv ψ) (Set.Icc x y) := by
  have hlog : ContinuousOn log (Set.Icc x y) := continuousOn_log.mono fun t ht ↦ by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith [ht.1]
  unfold cosineWeightDeriv
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro t ht
  have : 0 < t := by linarith [ht.1]
  have : 0 < log t := log_pos (by linarith [ht.1])
  positivity

theorem abs_cosineWeight_le (ψ : ℝ) {t : ℝ} (ht : 1 < t) :
    |cosineWeight ψ t| ≤ (t * log t)⁻¹ := by
  have ht0 : 0 < t := by linarith
  have hl0 : 0 < log t := log_pos ht
  rw [cosineWeight, abs_mul, abs_of_pos (inv_pos.2 (mul_pos ht0 hl0))]
  exact mul_le_of_le_one_left (by positivity) (abs_cos_le_one _)

theorem abs_cosineWeightDeriv_le {ψ t : ℝ} (hψ : |ψ| ≤ 2) (ht : 1 < t) :
    |cosineWeightDeriv ψ t| ≤ 3 * ((log t + 1) / (t * log t) ^ 2) := by
  have ht0 : 0 < t := by linarith
  have hl0 := log_pos ht
  have h1 : |ψ * log t * sin (ψ * log t)| ≤ 2 * log t := by
    rw [abs_mul, abs_mul, abs_of_pos hl0]
    calc |ψ| * log t * |sin (ψ * log t)| ≤ 2 * log t * 1 := by
          gcongr
          exact abs_sin_le_one _
      _ = 2 * log t := mul_one _
  have h2 : |(log t + 1) * cos (ψ * log t)| ≤ log t + 1 := by
    rw [abs_mul, abs_of_pos (by linarith)]
    exact mul_le_of_le_one_right (by linarith) (abs_cos_le_one _)
  rw [cosineWeightDeriv, abs_div, abs_neg, abs_of_nonneg (sq_nonneg (t * log t))]
  have hnum := abs_add_le (ψ * log t * sin (ψ * log t)) ((log t + 1) * cos (ψ * log t))
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)

/-- The prime cosine sum with the weak cutoff used in (2.12). -/
noncomputable def cosinePrimeSum (x ψ : ℝ) : ℝ :=
  ∑ k ∈ range (⌊x⌋₊ + 1), if k.Prime then cos (ψ * log k) / k else 0

theorem cosinePrimeSum_sub {x y : ℝ} (hxy : x ≤ y) (ψ : ℝ) :
    cosinePrimeSum y ψ - cosinePrimeSum x ψ =
      ∑ k ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, cosineWeight ψ k * logPrime k := by
  rw [cosinePrimeSum, cosinePrimeSum, ← sum_Ico_eq_sub _ (by gcongr),
    Finset.Ico_add_one_add_one_eq_Ioc]
  refine sum_congr rfl fun k _ ↦ ?_
  unfold logPrime cosineWeight
  split_ifs with hk
  · have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne_zero
    have hl0 : log k ≠ 0 := (log_pos (by exact_mod_cast hk.one_lt)).ne'
    field_simp
  · simp

/-- Uniform in both endpoints and in frequencies, including frequency zero. -/
theorem cosinePrimeSum_interval_error : ∃ K ≥ 0, ∀ x y ψ,
    2 ≤ x → x ≤ y → |ψ| ≤ 2 →
    |cosinePrimeSum y ψ - cosinePrimeSum x ψ - (∫ t in x..y, cosineWeight ψ t)| ≤
      K * pntE x := by
  obtain ⟨K, hK0, hK⟩ := weighted_prime_error_bound
  refine ⟨K * 4, by positivity, fun x y ψ hx hxy hψ ↦ ?_⟩
  rw [cosinePrimeSum_sub hxy]
  have h := hK hx hxy (by norm_num : (0 : ℝ) ≤ 3)
    (fun t ht ↦ hasDerivAt_cosineWeight ψ (by linarith [ht.1]))
    (continuousOn_cosineWeightDeriv ψ (by linarith))
    (fun t ht ↦ abs_cosineWeight_le ψ (by linarith [ht.1]))
    (fun t ht ↦ abs_cosineWeightDeriv_le hψ (by linarith [ht.1]))
  norm_num only [show (1 : ℝ) + 3 = 4 by norm_num] at h
  exact h

theorem cosinePrimeSum_two (ψ : ℝ) : cosinePrimeSum 2 ψ = cos (ψ * log 2) / 2 := by
  norm_num [cosinePrimeSum, sum_range_succ]

/-- The number-theoretic input in (2.12): a uniformly bounded difference from
`∫₂ˣ cos(ψ log t)/(t log t) dt`. Evaluating that integral is a separate analytic step. -/
theorem cosinePrimeSum_integral_error : ∃ K ≥ 0, ∀ x ψ,
    2 ≤ x → |ψ| ≤ 2 →
    |cosinePrimeSum x ψ - (∫ t in 2..x, cosineWeight ψ t)| ≤ K := by
  obtain ⟨K, hK0, hK⟩ := cosinePrimeSum_interval_error
  refine ⟨K + 1, by positivity, fun x ψ hx hψ ↦ ?_⟩
  have he := hK 2 x ψ le_rfl hx hψ
  have h2 : |cosinePrimeSum 2 ψ| ≤ 1 := by
    rw [cosinePrimeSum_two, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have := abs_cos_le_one (ψ * log 2)
    linarith
  calc |cosinePrimeSum x ψ - (∫ t in 2..x, cosineWeight ψ t)|
      ≤ |cosinePrimeSum x ψ - cosinePrimeSum 2 ψ - (∫ t in 2..x, cosineWeight ψ t)| +
        |cosinePrimeSum 2 ψ| := by
          convert abs_add_le
            (cosinePrimeSum x ψ - cosinePrimeSum 2 ψ - (∫ t in 2..x, cosineWeight ψ t))
            (cosinePrimeSum 2 ψ) using 1
          congr 1
          ring
    _ ≤ K * pntE 2 + 1 := add_le_add he h2
    _ ≤ K + 1 := by nlinarith [pntE_le_one 2]

end BretecheTenenbaumMean.PrimeSums
