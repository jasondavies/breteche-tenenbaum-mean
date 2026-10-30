module

public import BretecheTenenbaumMean.HighFrequencyLogWeight

@[expose] public section

/-! # Majorants near and away from the frequency diagonal -/

namespace BretecheTenenbaumMean

open Real

/-- Absorb the slowly varying factor into a rational power below `3/2`. -/
theorem regularizedHighKernel_power_bound {ε θ φ : ℝ}
    (hε : 0 ≤ ε) (hθ : 0 < θ) (hθφ : θ ≤ φ) (hφ1 : φ ≤ 1) :
    regularizedHighKernel ε θ φ ≤
      3 * (φ / θ) ^ (95 / 64 : ℝ) * (θ + ε) /
        (sqrt θ * φ ^ 2 * sqrt (φ - θ + ε) * sqrt (log (3 / θ))) := by
  have hφ : 0 < φ := hθ.trans_le hθφ
  have hd : 0 ≤ (θ + ε) / (sqrt θ * φ ^ 2 * sqrt (φ - θ + ε)) := by positivity
  have h := mul_le_mul_of_nonneg_right (frequency_power_log_le hθ hθφ hφ1) hd
  unfold regularizedHighKernel
  convert h using 1 <;> ring

/-- In the near range only an integrable square-root singularity remains. -/
theorem regularizedHighKernel_near {ε θ φ : ℝ}
    (hε : 0 < ε) (hεθ : ε ≤ θ) (hθ : 0 < θ) (hθφ : θ ≤ φ)
    (hφ2 : φ ≤ 2 * θ) (hφ1 : φ ≤ 1) :
    regularizedHighKernel ε θ φ ≤
      (24 / (θ * sqrt θ * sqrt (log (3 / θ)))) * (sqrt (φ - θ + ε))⁻¹ := by
  have hφ : 0 < φ := hθ.trans_le hθφ
  have hd : 0 < sqrt (φ - θ + ε) := sqrt_pos.2 (by linarith)
  have hL : 0 < sqrt (log (3 / θ)) :=
    sqrt_pos.2 (log_pos ((lt_div_iff₀ hθ).2 (by linarith)))
  have hr : 0 ≤ φ / θ := div_nonneg hφ.le hθ.le
  have hr2 : φ / θ ≤ 2 := (div_le_iff₀ hθ).2 (by linarith)
  have hp : (φ / θ) ^ (95 / 64 : ℝ) ≤ 4 := by
    calc _ ≤ (2 : ℝ) ^ (95 / 64 : ℝ) := rpow_le_rpow hr hr2 (by norm_num)
      _ ≤ (2 : ℝ) ^ (2 : ℝ) := rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := by norm_num
  have hn : 3 * (φ / θ) ^ (95 / 64 : ℝ) * (θ + ε) ≤ 24 * θ := by
    have h := mul_le_mul (mul_le_mul_of_nonneg_left hp (by norm_num))
      (show θ + ε ≤ 2 * θ by linarith) (by linarith : 0 ≤ θ + ε) (by norm_num : (0 : ℝ) ≤ 3 * 4)
    nlinarith
  have hden : sqrt θ * θ ^ 2 * sqrt (φ - θ + ε) * sqrt (log (3 / θ)) ≤
      sqrt θ * φ ^ 2 * sqrt (φ - θ + ε) * sqrt (log (3 / θ)) := by
    gcongr
  refine (regularizedHighKernel_power_bound hε.le hθ hθφ hφ1).trans ?_
  calc _ ≤ (24 * θ) / (sqrt θ * θ ^ 2 * sqrt (φ - θ + ε) * sqrt (log (3 / θ))) :=
      div_le_div₀ (by positivity) hn (by positivity) hden
    _ = _ := by field_simp

/-- Away from the diagonal, a power of exponent strictly below `-1` is enough.
The gap `1/64` is explicit and independent of all parameters. -/
theorem regularizedHighKernel_far {ε θ φ : ℝ}
    (hε : 0 < ε) (hεθ : ε ≤ θ) (hθ : 0 < θ)
    (hφ2 : 2 * θ ≤ φ) (hφ1 : φ ≤ 1) :
    regularizedHighKernel ε θ φ ≤
      (12 * θ ^ (-63 / 64 : ℝ) / sqrt (log (3 / θ))) * φ ^ (-65 / 64 : ℝ) := by
  have hθφ : θ ≤ φ := by linarith
  have hφ : 0 < φ := hθ.trans_le hθφ
  have hd : 0 < sqrt (φ - θ + ε) := sqrt_pos.2 (by linarith)
  have hL : 0 < sqrt (log (3 / θ)) :=
    sqrt_pos.2 (log_pos ((lt_div_iff₀ hθ).2 (by linarith)))
  have hs : sqrt φ / 2 ≤ sqrt (φ - θ + ε) := by
    apply (le_sqrt (by positivity) (by linarith)).2
    rw [div_pow, sq_sqrt hφ.le]
    nlinarith
  have hn : 3 * (φ / θ) ^ (95 / 64 : ℝ) * (θ + ε) ≤
      6 * θ * (φ / θ) ^ (95 / 64 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (show θ + ε ≤ 2 * θ by linarith)
      (show 0 ≤ 3 * (φ / θ) ^ (95 / 64 : ℝ) by positivity)
    nlinarith
  have hden : sqrt θ * φ ^ 2 * (sqrt φ / 2) * sqrt (log (3 / θ)) ≤
      sqrt θ * φ ^ 2 * sqrt (φ - θ + ε) * sqrt (log (3 / θ)) := by
    gcongr
  have hφpow : φ ^ (-65 / 64 : ℝ) * φ ^ 2 * sqrt φ = φ ^ (95 / 64 : ℝ) := by
    rw [sqrt_eq_rpow, ← rpow_natCast φ 2, ← rpow_add hφ, ← rpow_add hφ]
    norm_num
  have hθpow : θ ^ (-63 / 64 : ℝ) * sqrt θ * θ ^ (95 / 64 : ℝ) = θ := by
    rw [sqrt_eq_rpow, ← rpow_add hθ, ← rpow_add hθ]
    norm_num
  refine (regularizedHighKernel_power_bound hε.le hθ hθφ hφ1).trans ?_
  calc _ ≤ (6 * θ * (φ / θ) ^ (95 / 64 : ℝ)) /
        (sqrt θ * φ ^ 2 * (sqrt φ / 2) * sqrt (log (3 / θ))) :=
      div_le_div₀ (by positivity) hn (by positivity) hden
    _ = _ := by
      rw [div_rpow hφ.le hθ.le]
      field_simp
      calc _ = 12 * (θ ^ (-63 / 64 : ℝ) * sqrt θ * θ ^ (95 / 64 : ℝ)) *
          (φ ^ (-65 / 64 : ℝ) * φ ^ 2 * sqrt φ) := by rw [hθpow, hφpow]; ring
        _ = _ := by ring_nf

end BretecheTenenbaumMean
