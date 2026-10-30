module

public import BretecheTenenbaumMean.LogarithmicPenaltyIntegral

@[expose] public section

/-! # The logarithmic integral in the third-moment base case -/

namespace BretecheTenenbaumMean

open Real MeasureTheory

/-- An integrable exponential transition, with its exact logarithmic bound. -/
theorem integral_logistic_le {a R u v : ℝ} (ha : 0 < a) (hR : 0 ≤ R) (hu : 0 ≤ u) :
    (∫ s in u..v, R / (R + exp (a * s))) ≤ log (1 + R) / a := by
  have hd : ∀ s : ℝ,
      HasDerivAt (fun s : ℝ ↦ -log (1 + R * exp (-a * s)) / a) (R / (R + exp (a * s))) s := by
    intro s
    have he : 0 < exp (a * s) := exp_pos _
    have he' : 0 < exp (-a * s) := exp_pos _
    have hden : 0 < 1 + R * exp (-a * s) := by positivity
    convert (((((hasDerivAt_id s).const_mul (-a)).exp.const_mul R).const_add 1).log hden.ne').neg.div_const a using 1
    · rfl
    · simp only [id_eq, mul_one, neg_mul, exp_neg]
      field_simp
      ring
  have hc : Continuous (fun s : ℝ ↦ R / (R + exp (a * s))) := by
    apply Continuous.div continuous_const (by fun_prop)
    intro s
    positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hd s) (hc.intervalIntegrable _ _)]
  have hv : 0 ≤ log (1 + R * exp (-a * v)) := log_nonneg (le_add_of_nonneg_right (mul_nonneg hR (exp_pos _).le))
  have heu : exp (-a * u) ≤ 1 := exp_le_one_iff.2 (by nlinarith)
  have hlu : log (1 + R * exp (-a * u)) ≤ log (1 + R) :=
    log_le_log (by positivity) (by nlinarith)
  have hdiv := div_le_div_of_nonneg_right hlu ha.le
  have hneg : 0 ≤ log (1 + R * exp (-a * v)) / a := div_nonneg hv ha.le
  simp only [neg_div, sub_neg_eq_add]
  linarith

/-- Substitution in the logarithmic measure, with an arbitrary positive saving. -/
theorem integral_logarithmic_transition_le {a R X : ℝ}
    (ha : 0 < a) (hR : 0 ≤ R) (hX : 1 ≤ X) :
    (∫ y in 1..X, (R / (R + log (3 * y) ^ a)) / (y * log (3 * y))) ≤
      log (1 + R) / a := by
  let g := fun s : ℝ ↦ R / (R + exp (a * s))
  have hg : Continuous g := by
    dsimp only [g]
    apply Continuous.div continuous_const (by fun_prop)
    intro s
    positivity
  have he : (∫ y in 1..X, (R / (R + log (3 * y) ^ a)) / (y * log (3 * y))) =
      ∫ y in 1..X, g (log (log (3 * y))) / (y * log (3 * y)) := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hX]
    intro y hy
    have hl : 0 < log (3 * y) := log_pos (by linarith [hy.1])
    dsimp only [g]
    rw [rpow_def_of_pos hl, mul_comm (log (log (3 * y))) a]
  rw [he, integral_loglog_substitution hX hg]
  have h3 : 1 ≤ log 3 := by linarith [log_three_gt_d9]
  exact integral_logistic_le ha hR (log_nonneg h3)

theorem intervalIntegrable_logarithmic_transition {a R X : ℝ}
    (hR : 0 ≤ R) (hX : 1 ≤ X) :
    IntervalIntegrable (fun y : ℝ ↦ (R / (R + log (3 * y) ^ a)) / (y * log (3 * y))) volume 1 X := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hX]
  intro y hy
  have hy0 : 0 < y := by linarith [hy.1]
  have hl : 0 < log (3 * y) := log_pos (by linarith [hy.1])
  have hr : 0 < log (3 * y) ^ a := rpow_pos_of_pos hl _
  have hcL : ContinuousAt (fun y : ℝ ↦ log (3 * y)) y := by fun_prop (disch := positivity)
  have hcR := hcL.rpow_const (p := a) (Or.inl hl.ne')
  exact ((continuousAt_const.div (continuousAt_const.add hcR) (show R + log (3 * y) ^ a ≠ 0 by positivity)).div
    (continuousAt_id.mul hcL) (show y * log (3 * y) ≠ 0 by positivity)).continuousWithinAt

end BretecheTenenbaumMean
