module

public import BretecheTenenbaumMean.PrimeSmoothingTail
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! # Factorial bounds for logarithmic power integrals -/

namespace BretecheTenenbaumMean

open Real MeasureTheory

/-- An exponential-series bound with a uniform factorial constant. -/
theorem log_three_mul_pow_le {y : ℝ} (hy : 1 ≤ y) (k : ℕ) :
    log (3 * y) ^ k ≤ 3 * 8 ^ k * (k.factorial : ℝ) * y ^ (1 / 8 : ℝ) := by
  have hy0 : 0 < y := by linarith
  have hlog : 0 ≤ log (3 * y) := log_nonneg (by linarith)
  have hf : 0 < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have h := pow_div_factorial_le_exp (log (3 * y) / 8) (by positivity) k
  have he : exp (log (3 * y) / 8) ≤ 3 * y ^ (1 / 8 : ℝ) := by
    conv_rhs => lhs; rw [← exp_log (by norm_num : (0 : ℝ) < 3)]
    rw [rpow_def_of_pos hy0, ← exp_add]
    apply exp_le_exp.2
    rw [log_mul (by norm_num) hy0.ne']
    have h3 : 0 ≤ log 3 := log_nonneg (by norm_num)
    linarith
  have hh := mul_le_mul_of_nonneg_right (h.trans he) (mul_pos (by positivity : (0 : ℝ) < 8 ^ k) hf).le
  rw [div_pow] at hh
  have heq : (log (3 * y) ^ k / 8 ^ k / (k.factorial : ℝ)) * (8 ^ k * k.factorial) =
      log (3 * y) ^ k := by field_simp
  rw [heq] at hh
  nlinarith

/-- The residual power decay after applying the exponential-series bound. -/
theorem rpow_eighth_div {y : ℝ} (hy : 0 < y) :
    y ^ (1 / 8 : ℝ) / (y * y ^ (1 / 4 : ℝ)) = y ^ (-9 / 8 : ℝ) := by
  conv_lhs => rhs; lhs; rw [← rpow_one y]
  rw [← rpow_add hy, ← rpow_sub hy]
  norm_num

theorem intervalIntegrable_logPowerKernel (k : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    IntervalIntegrable (fun y : ℝ ↦ log (3 * y) ^ k / (y * y ^ (1 / 4 : ℝ))) volume 1 X := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hX]
  intro y hy
  have hy0 : 0 < y := by linarith [hy.1]
  have hr : 0 < y ^ (1 / 4 : ℝ) := rpow_pos_of_pos hy0 _
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := positivity)

/-- A factorial bound, uniform in the upper endpoint and the power. -/
theorem integral_logPowerKernel_le (k : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    (∫ y in 1..X, log (3 * y) ^ k / (y * y ^ (1 / 4 : ℝ))) ≤
      24 * 8 ^ k * (k.factorial : ℝ) := by
  have hc : ContinuousOn (fun y : ℝ ↦ y ^ (-9 / 8 : ℝ)) (Set.uIcc 1 X) := by
    rw [Set.uIcc_of_le hX]
    intro y hy
    have hy0 : 0 < y := by linarith [hy.1]
    exact (continuousAt_rpow_const y (-9 / 8) (Or.inl hy0.ne')).continuousWithinAt
  have hpow : (∫ y in 1..X, y ^ (-9 / 8 : ℝ)) ≤ 8 := by
    rw [integral_rpow (Or.inr ⟨by norm_num, by
      rw [Set.uIcc_of_le hX]; simp⟩)]
    norm_num
    have hnonneg : 0 ≤ X ^ (-1 / 8 : ℝ) := rpow_nonneg (by linarith) _
    linarith
  have hi := intervalIntegral.integral_mono_on hX (intervalIntegrable_logPowerKernel k hX)
    (hc.intervalIntegrable.const_mul (3 * 8 ^ k * (k.factorial : ℝ))) (fun y hy ↦ by
      have hy0 : 0 < y := by linarith [hy.1]
      calc
        _ ≤ (3 * 8 ^ k * (k.factorial : ℝ) * y ^ (1 / 8 : ℝ)) / (y * y ^ (1 / 4 : ℝ)) :=
          div_le_div_of_nonneg_right (log_three_mul_pow_le hy.1 k) (by positivity)
        _ = (3 * 8 ^ k * (k.factorial : ℝ)) * y ^ (-9 / 8 : ℝ) := by
          rw [mul_div_assoc, rpow_eighth_div hy0])
  rw [intervalIntegral.integral_const_mul] at hi
  have hm := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 3 * 8 ^ k * (k.factorial : ℝ))
  nlinarith

end BretecheTenenbaumMean
