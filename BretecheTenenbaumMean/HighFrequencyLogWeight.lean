module

public import BretecheTenenbaumMean.HighFrequencyKernel

@[expose] public section

/-! # Absorbing the slowly varying logarithm in a small power -/

namespace BretecheTenenbaumMean

open Real

/-- A logarithm grows more slowly than any positive real power, with the
constant and the subtraction retained. -/
theorem log_le_rpow_sub_one {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    log r ≤ (r ^ s - 1) / s := by
  have h := log_le_sub_one_of_pos (rpow_pos_of_pos hr s)
  rw [log_rpow hr] at h
  exact (le_div_iff₀ hs).2 (by nlinarith)

/-- The logarithmic square-root weight can be transferred to the smaller
frequency at the cost of the small power `1/16`. -/
theorem sqrt_frequency_log_le {θ φ : ℝ} (hθ : 0 < θ) (hθφ : θ ≤ φ) (hφ1 : φ ≤ 1) :
    sqrt (log (3 / θ)) ≤ 3 * (φ / θ) ^ (1 / 16 : ℝ) * sqrt (log (3 / φ)) := by
  have hφ : 0 < φ := hθ.trans_le hθφ
  have hr : 0 < φ / θ := div_pos hφ hθ
  have hr1 : 1 ≤ φ / θ := (one_le_div hθ).2 hθφ
  have hL : 1 ≤ log (3 / φ) := by
    have h3 : 1 ≤ log 3 := by linarith [log_three_gt_d9]
    exact h3.trans (log_le_log (by norm_num) ((le_div_iff₀ hφ).2 (by linarith)))
  have he : log (3 / θ) = log (3 / φ) + log (φ / θ) := by
    rw [← log_mul (div_ne_zero (by norm_num) hφ.ne') hr.ne']
    congr 1
    field_simp
  have hp : 1 ≤ (φ / θ) ^ (1 / 8 : ℝ) := one_le_rpow hr1 (by norm_num)
  have hlog := log_le_rpow_sub_one hr (show (0 : ℝ) < 1 / 8 by norm_num)
  have hcmp : log (3 / θ) ≤ 9 * (φ / θ) ^ (1 / 8 : ℝ) * log (3 / φ) := by
    rw [he]
    nlinarith [mul_nonneg (sub_nonneg.2 hp) (sub_nonneg.2 hL)]
  apply (sqrt_le_left (by positivity)).2
  rw [mul_pow, mul_pow, sq_sqrt (by linarith : 0 ≤ log (3 / φ)),
    ← rpow_natCast ((φ / θ) ^ (1 / 16 : ℝ)) 2, ← rpow_mul hr.le]
  norm_num
  exact hcmp

/-- A rational exponent below `3/2` absorbs both the prime-sum exponent and
the logarithmic transfer. The remaining gap is essential for integration. -/
theorem frequency_power_log_le {θ φ : ℝ} (hθ : 0 < θ) (hθφ : θ ≤ φ) (hφ1 : φ ≤ 1) :
    (φ / θ) ^ sqrt 2 / sqrt (log (3 / φ)) ≤
      3 * (φ / θ) ^ (95 / 64 : ℝ) / sqrt (log (3 / θ)) := by
  have hφ : 0 < φ := hθ.trans_le hθφ
  have hr : 0 < φ / θ := div_pos hφ hθ
  have hr1 : 1 ≤ φ / θ := (one_le_div hθ).2 hθφ
  have hLφ : 0 < sqrt (log (3 / φ)) := sqrt_pos.2 (log_pos ((lt_div_iff₀ hφ).2 (by linarith)))
  have hLθ : 0 < sqrt (log (3 / θ)) := sqrt_pos.2 (log_pos ((lt_div_iff₀ hθ).2 (by linarith)))
  have hs : sqrt (2 : ℝ) ≤ 91 / 64 := (sqrt_le_left (by norm_num)).2 (by norm_num)
  have hp : (φ / θ) ^ (sqrt 2 + 1 / 16) ≤ (φ / θ) ^ (95 / 64 : ℝ) :=
    rpow_le_rpow_of_exponent_le hr1 (by linarith)
  rw [div_le_div_iff₀ hLφ hLθ]
  calc (φ / θ) ^ sqrt 2 * sqrt (log (3 / θ))
      ≤ (φ / θ) ^ sqrt 2 * (3 * (φ / θ) ^ (1 / 16 : ℝ) * sqrt (log (3 / φ))) :=
        mul_le_mul_of_nonneg_left (sqrt_frequency_log_le hθ hθφ hφ1) (rpow_pos_of_pos hr _).le
    _ = 3 * (φ / θ) ^ (sqrt 2 + 1 / 16) * sqrt (log (3 / φ)) := by
      rw [rpow_add hr]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num)) hLφ.le

end BretecheTenenbaumMean
