module

public import BretecheTenenbaumMean.GoodSets
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! # The small-frequency branch of the good-set penalty -/

namespace BretecheTenenbaumMean

open Real

theorem criticalSlope_pos : 0 < criticalSlope := by
  unfold criticalSlope
  have hl : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    norm_num
  have := log_two_gt_d9
  apply div_pos (by norm_num)
  linarith

theorem criticalSlope_le_three : criticalSlope ≤ 3 := by
  unfold criticalSlope
  have hl : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    norm_num
  have := log_two_gt_d9
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- A fixed numerical margin selects the logarithmic branch of the penalty. -/
theorem penalty_quadratic_dominates {t u : ℝ} (ht : 0 < t) (hu : 16 * t ≤ u) :
    t + u ≤ (u - criticalSlope * t) ^ 2 / t := by
  have hb0 := criticalSlope_pos
  have hb3 := criticalSlope_le_three
  have hbt : criticalSlope * t ≤ 3 * t := mul_le_mul_of_nonneg_right hb3 ht.le
  have hd : u / 2 ≤ u - criticalSlope * t := by linarith
  have hu0 : 0 ≤ u := by linarith
  have hs : (u / 2) ^ 2 ≤ (u - criticalSlope * t) ^ 2 := by
    exact sq_le_sq₀ (by positivity) (by linarith) |>.2 hd
  rw [le_div_iff₀ ht]
  nlinarith [mul_nonneg (sub_nonneg.2 hu) hu0, mul_nonneg (show 0 ≤ u - t by linarith) ht.le]

/-- Exact penalty in the far small-frequency range. -/
theorem penalty_eq_log {δ T y : ℝ} (hT : 1 < T) (hy : 1 ≤ y)
    (hlarge : 16 * log T ≤ log (log (3 * y))) :
    penalty δ T y = δ * log (T * log (3 * y)) := by
  have hT0 : 0 < T := by linarith
  have hL : 0 < log (3 * y) := log_pos (by linarith)
  have h := penalty_quadratic_dominates (log_pos hT) hlarge
  rw [penalty, min_eq_left]
  rwa [log_mul hT0.ne' hL.ne']

/-- The corresponding good-set envelope is a real power. -/
theorem penalty_envelope_eq_rpow {δ T y : ℝ} (hT : 1 < T) (hy : 1 ≤ y)
    (hlarge : 16 * log T ≤ log (log (3 * y))) :
    T * log (3 * y) * exp (-penalty δ T y) = (T * log (3 * y)) ^ (1 - δ) := by
  have hp : 0 < T * log (3 * y) := mul_pos (by linarith) (log_pos (by linarith))
  rw [penalty_eq_log hT hy hlarge, rpow_def_of_pos hp]
  calc _ = exp (log (T * log (3 * y))) * exp (-(δ * log (T * log (3 * y)))) := by
          rw [exp_log hp]
       _ = _ := by rw [← exp_add]; congr 1; ring

/-- `θ ≤ T⁻¹⁶` implies the required large logarithmic separation. -/
theorem frequency_penalty_large {T θ : ℝ} (hT : 1 < T) (hθ : 0 < θ)
    (hsmall : θ ≤ T ^ (-16 : ℝ)) :
    16 * log T ≤ log (log (3 * exp θ⁻¹)) := by
  have hT0 : 0 < T := by linarith
  have hlog := log_le_log hθ hsmall
  rw [log_rpow hT0] at hlog
  have h3 : 0 < log 3 := log_pos (by norm_num)
  have hinside : θ⁻¹ ≤ log (3 * exp θ⁻¹) := by
    rw [log_mul (by norm_num : (3 : ℝ) ≠ 0) (exp_ne_zero _), log_exp]
    linarith
  have h := log_le_log (inv_pos.2 hθ) hinside
  rw [log_inv] at h
  linarith

/-- A convenient power majorant, keeping all constants uniform in `T` and `θ`. -/
theorem frequency_penalty_envelope_le {δ T θ : ℝ} (hδ : δ ≤ 1) (hT : 1 < T)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hsmall : θ ≤ T ^ (-16 : ℝ)) :
    T * log (3 * exp θ⁻¹) * exp (-penalty δ T (exp θ⁻¹)) ≤
      (4 : ℝ) ^ (1 - δ) * T ^ (1 - δ) * θ ^ (δ - 1) := by
  have hT0 : 0 < T := by linarith
  have hy : 1 ≤ exp θ⁻¹ := one_le_exp_iff.2 (inv_nonneg.2 hθ.le)
  rw [penalty_envelope_eq_rpow hT hy (frequency_penalty_large hT hθ hsmall)]
  have hLpos : 0 ≤ T * log (3 * exp θ⁻¹) :=
    mul_nonneg hT0.le (log_nonneg (by linarith))
  have hL : log (3 * exp θ⁻¹) ≤ 4 / θ := by
    rw [log_mul (by norm_num : (3 : ℝ) ≠ 0) (exp_ne_zero _), log_exp]
    have hl3 := log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    have hinv : 1 ≤ θ⁻¹ := (one_le_inv₀ hθ).2 hθ1
    rw [div_eq_mul_inv]
    linarith
  calc (T * log (3 * exp θ⁻¹)) ^ (1 - δ) ≤ (4 * T / θ) ^ (1 - δ) := by
          apply rpow_le_rpow hLpos _ (by linarith)
          have h := mul_le_mul_of_nonneg_left hL hT0.le
          convert h using 1
          ring
       _ = (4 : ℝ) ^ (1 - δ) * T ^ (1 - δ) * θ ^ (δ - 1) := by
          rw [div_rpow (by positivity) hθ.le, mul_rpow (by norm_num) hT0.le]
          rw [show δ - 1 = -(1 - δ) by ring, rpow_neg hθ.le, div_eq_mul_inv]

end BretecheTenenbaumMean
