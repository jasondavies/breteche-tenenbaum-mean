module

public import BretecheTenenbaumMean.PenaltyIntegral

@[expose] public section

/-! # The logarithmic penalty integral in the moment induction -/

namespace BretecheTenenbaumMean

open Real MeasureTheory

/-- An exponentially decaying tail on a nonnegative interval. -/
theorem integral_exp_neg_mul_le {δ a b : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) :
    (∫ s in a..b, exp (-δ * s)) ≤ 1 / δ := by
  have hd : ∀ s : ℝ, HasDerivAt (fun s ↦ exp (-δ * s) / (-δ)) (exp (-δ * s)) s := by
    intro s
    convert (((hasDerivAt_id s).const_mul (-δ)).exp.div_const (-δ)) using 1
    · rfl
    · simp only [id_eq, mul_one]
      field_simp [hδ.ne']
  have hc : Continuous (fun s : ℝ ↦ exp (-δ * s)) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hd s) (hc.intervalIntegrable _ _)]
  have haexp : exp (-δ * a) ≤ 1 := exp_le_one_iff.2 (by nlinarith)
  have hbexp := exp_pos (-δ * b)
  calc
    _ = (exp (-δ * a) - exp (-δ * b)) / δ := by ring
    _ ≤ 1 / δ := div_le_div_of_nonneg_right (by linarith) hδ.le

/-- Integrating the clipped penalty in its logarithmic coordinate costs
at most a constant plus the Gaussian width `sqrt t`. -/
theorem integral_clipped_penalty_le {δ t a b : ℝ} (hδ : 0 < δ) (ht : 0 < t)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ s in a..b, exp (-(δ * min (t + s) ((s - criticalSlope * t) ^ 2 / t)))) ≤
      1 / δ + sqrt (π / δ) * sqrt t := by
  have hf : Continuous (fun s : ℝ ↦ exp (-(δ * min (t + s) ((s - criticalSlope * t) ^ 2 / t)))) := by fun_prop
  have hg : Continuous (fun s : ℝ ↦ exp (-δ * s)) := by fun_prop
  have hh : Continuous (fun s : ℝ ↦ exp (-(δ / t) * (s - criticalSlope * t) ^ 2)) := by fun_prop
  have hpoint : ∀ s : ℝ, exp (-(δ * min (t + s) ((s - criticalSlope * t) ^ 2 / t))) ≤
      exp (-δ * s) + exp (-(δ / t) * (s - criticalSlope * t) ^ 2) := by
    intro s
    rcases le_total (t + s) ((s - criticalSlope * t) ^ 2 / t) with h | h
    · rw [min_eq_left h]
      exact (exp_le_exp.2 (by nlinarith [mul_pos hδ ht])).trans
        (le_add_of_nonneg_right (exp_pos _).le)
    · rw [min_eq_right h]
      have he : -(δ * ((s - criticalSlope * t) ^ 2 / t)) =
          -(δ / t) * (s - criticalSlope * t) ^ 2 := by ring
      rw [he]
      exact le_add_of_nonneg_left (exp_pos _).le
  have h := intervalIntegral.integral_mono_on hab (hf.intervalIntegrable (μ := volume) _ _)
    ((hg.add hh).intervalIntegrable _ _) (fun s _ ↦ hpoint s)
  simp only [Pi.add_apply] at h
  rw [intervalIntegral.integral_add (hg.intervalIntegrable _ _) (hh.intervalIntegrable _ _)] at h
  have he : sqrt (π / (δ / t)) = sqrt (π / δ) * sqrt t := by
    rw [← sqrt_mul (by positivity : 0 ≤ π / δ)]
    congr 1
    field_simp
  exact h.trans (he ▸ add_le_add (integral_exp_neg_mul_le hδ ha)
    (integral_translated_gaussian_le (div_pos hδ ht) hab _))

/-- Differentiating the exact logarithmic coordinate of the envelope. -/
theorem hasDerivAt_loglog_three_mul {y : ℝ} (hy : 1 ≤ y) :
    HasDerivAt (fun y : ℝ ↦ log (log (3 * y))) (1 / (y * log (3 * y))) y := by
  have hy0 : 0 < y := by linarith
  have hL : 0 < log (3 * y) := log_pos (by linarith)
  have hd := (((hasDerivAt_id y).const_mul 3).log (by positivity : 3 * y ≠ 0)).log hL.ne'
  convert hd using 1
  · rfl
  · simp only [id_eq, mul_one]
    field_simp

/-- Substitution in the logarithmic measure used by (2.19). -/
theorem integral_loglog_substitution {X : ℝ} (hX : 1 ≤ X) {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ y in 1..X, g (log (log (3 * y))) / (y * log (3 * y))) =
      ∫ s in log (log 3)..log (log (3 * X)), g s := by
  have hd : ∀ y ∈ Set.uIcc 1 X,
      HasDerivAt (fun y : ℝ ↦ log (log (3 * y))) (1 / (y * log (3 * y))) y := by
    rw [Set.uIcc_of_le hX]
    exact fun y hy ↦ hasDerivAt_loglog_three_mul hy.1
  have hc : ContinuousOn (fun y : ℝ ↦ 1 / (y * log (3 * y))) (Set.uIcc 1 X) := by
    rw [Set.uIcc_of_le hX]
    intro y hy
    have hy0 : 0 < y := by linarith [hy.1]
    have hL : 0 < log (3 * y) := log_pos (by linarith [hy.1])
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  simpa only [Function.comp_def, mul_one, mul_one_div, mul_one] using
    intervalIntegral.integral_comp_mul_deriv hd hc hg

/-- The penalty integral needed in (2.19), uniformly in the upper endpoint. -/
theorem logarithmic_penalty_integral_le {δ T X : ℝ} (hδ : 0 < δ) (hT : 1 < T) (hX : 1 ≤ X) :
    (∫ y in 1..X, exp (-penalty δ T y) / (y * log (3 * y))) ≤
      1 / δ + sqrt (π / δ) * sqrt (log T) := by
  let g := fun s : ℝ ↦ exp (-(δ * min (log T + s) ((s - criticalSlope * log T) ^ 2 / log T)))
  have hg : Continuous g := by dsimp only [g]; fun_prop
  have he : (∫ y in 1..X, exp (-penalty δ T y) / (y * log (3 * y))) =
      ∫ y in 1..X, g (log (log (3 * y))) / (y * log (3 * y)) := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hX]
    intro y hy
    have hL : 0 < log (3 * y) := log_pos (by linarith [hy.1])
    dsimp only [g, penalty]
    rw [log_mul (by linarith : T ≠ 0) hL.ne']
  rw [he, integral_loglog_substitution hX hg]
  have h3 : 1 ≤ log 3 := by linarith [log_three_gt_d9]
  exact integral_clipped_penalty_le hδ (log_pos hT) (log_nonneg h3)
    (log_le_log (by linarith) (log_le_log (by norm_num) (by linarith)))

/-- For `T ≥ 3` the additive constant is absorbed in `sqrt(log T)`. -/
theorem logarithmic_penalty_integral_bound {δ T X : ℝ}
    (hδ : 0 < δ) (hT : 3 ≤ T) (hX : 1 ≤ X) :
    (∫ y in 1..X, exp (-penalty δ T y) / (y * log (3 * y))) ≤
      (1 / δ + sqrt (π / δ)) * sqrt (log T) := by
  have ht : 1 ≤ log T := (show (1 : ℝ) ≤ log 3 by linarith [log_three_gt_d9]).trans
    (log_le_log (by norm_num) hT)
  have hs : 1 ≤ sqrt (log T) := by simpa only [sqrt_one] using sqrt_le_sqrt ht
  have h := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 1 / δ)
  have hi := logarithmic_penalty_integral_le hδ (by linarith : 1 < T) hX
  nlinarith

end BretecheTenenbaumMean
