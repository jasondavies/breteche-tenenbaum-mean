module

public import BretecheTenenbaumMean.HighFrequencyKernel
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

@[expose] public section

/-! # Gaussian control of the good-set penalty -/

namespace BretecheTenenbaumMean

open Real MeasureTheory

/-- Taking a square root of the logarithmic variable converts the quadratic
penalty to a translated Gaussian, uniformly in the parameter `t`. -/
theorem quartic_penalty_ge_gaussian {b t s : ℝ} (hb : 0 ≤ b) (ht : 0 < t) (hs : 0 ≤ s) :
    b * (s - sqrt (b * t)) ^ 2 ≤ (s ^ 2 - b * t) ^ 2 / t := by
  have hc := sq_sqrt (mul_nonneg hb ht.le)
  have hc0 := sqrt_nonneg (b * t)
  have hlarge : b * t ≤ (s + sqrt (b * t)) ^ 2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left hlarge (sq_nonneg (s - sqrt (b * t)))
  have he : (s ^ 2 - b * t) ^ 2 =
      (s - sqrt (b * t)) ^ 2 * (s + sqrt (b * t)) ^ 2 := by
    conv_lhs => rw [← hc]
    ring
  rw [le_div_iff₀ ht, he]
  nlinarith [hprod]

/-- The exponential of the minimum is bounded by a sum of two Gaussians. -/
theorem exp_penalty_min_le_gaussians {δ b t s : ℝ}
    (hδ : 0 ≤ δ) (hb : 0 ≤ b) (ht : 0 < t) (hs : 0 ≤ s) :
    exp (-(δ * min (t + s ^ 2) ((s ^ 2 - b * t) ^ 2 / t)) / 2) ≤
      exp (-(δ / 2) * s ^ 2) + exp (-(δ * b / 2) * (s - sqrt (b * t)) ^ 2) := by
  rcases le_total (t + s ^ 2) ((s ^ 2 - b * t) ^ 2 / t) with h | h
  · rw [min_eq_left h]
    have he : exp (-(δ * (t + s ^ 2)) / 2) ≤ exp (-(δ / 2) * s ^ 2) :=
      exp_le_exp.2 (by nlinarith [mul_nonneg hδ ht.le])
    exact he.trans (le_add_of_nonneg_right (exp_pos _).le)
  · rw [min_eq_right h]
    have hq := mul_le_mul_of_nonneg_left (quartic_penalty_ge_gaussian hb ht hs) hδ
    have he : exp (-(δ * ((s ^ 2 - b * t) ^ 2 / t)) / 2) ≤
        exp (-(δ * b / 2) * (s - sqrt (b * t)) ^ 2) := exp_le_exp.2 (by nlinarith)
    exact he.trans (le_add_of_nonneg_left (exp_pos _).le)

/-- The change of variable used for the final frequency integral. -/
noncomputable def penaltyCoordinate (θ : ℝ) : ℝ := sqrt (log (log 3 + θ⁻¹))

/-- Its positive Jacobian when the direction of integration is reversed. -/
noncomputable def penaltyJacobian (θ : ℝ) : ℝ :=
  1 / (2 * θ * (1 + θ * log 3) * penaltyCoordinate θ)

theorem penaltyCoordinate_pos {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    0 < penaltyCoordinate θ := by
  have hi : 1 ≤ θ⁻¹ := (one_le_inv₀ hθ).2 hθ1
  have h3 : 0 < log 3 := log_pos (by norm_num)
  exact sqrt_pos.2 (log_pos (by linarith))

theorem penaltyCoordinate_sq {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    penaltyCoordinate θ ^ 2 = log (log 3 + θ⁻¹) := by
  have hi : 1 ≤ θ⁻¹ := (one_le_inv₀ hθ).2 hθ1
  have h3 : 0 < log 3 := log_pos (by norm_num)
  exact sq_sqrt (log_nonneg (by linarith))

/-- The coordinate does not exceed the square-root logarithm in the kernel. -/
theorem penaltyCoordinate_le {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    penaltyCoordinate θ ≤ sqrt (log (3 / θ)) := by
  unfold penaltyCoordinate
  apply sqrt_le_sqrt
  apply log_le_log (by have := log_pos (by norm_num : (1 : ℝ) < 3); positivity)
  rw [le_div_iff₀ hθ]
  have hi : θ⁻¹ * θ = 1 := inv_mul_cancel₀ hθ.ne'
  have h3 : log 3 ≤ 2 := by linarith [log_three_lt_d9]
  nlinarith [mul_le_mul_of_nonneg_right h3 hθ.le]

/-- The exact good-set penalty in the new variable. -/
theorem penalty_eq_coordinate {δ T θ : ℝ} (hT : 0 < T) (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    penalty δ T (exp θ⁻¹) = δ * min (log T + penaltyCoordinate θ ^ 2)
      ((penaltyCoordinate θ ^ 2 - criticalSlope * log T) ^ 2 / log T) := by
  have hi : 1 ≤ θ⁻¹ := (one_le_inv₀ hθ).2 hθ1
  have h3 : 0 < log 3 := log_pos (by norm_num)
  rw [penalty, log_mul (by norm_num : (3 : ℝ) ≠ 0) (exp_ne_zero _), log_exp,
    log_mul hT.ne' (by positivity : log 3 + θ⁻¹ ≠ 0), penaltyCoordinate_sq hθ hθ1]

/-- The full penalty is dominated by a Gaussian centered at zero and one
centered at `√(b log T)`, with constants independent of `T`. -/
theorem frequency_penalty_le_gaussians {δ T θ : ℝ}
    (hδ : 0 ≤ δ) (hT : 1 < T) (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    exp (-penalty δ T (exp θ⁻¹) / 2) ≤
      exp (-(δ / 2) * penaltyCoordinate θ ^ 2) +
        exp (-(δ * criticalSlope / 2) * (penaltyCoordinate θ - sqrt (criticalSlope * log T)) ^ 2) := by
  rw [penalty_eq_coordinate (by linarith) hθ hθ1]
  exact exp_penalty_min_le_gaussians hδ criticalSlope_pos.le (log_pos hT)
    (penaltyCoordinate_pos hθ hθ1).le

/-- Differentiation of the exact coordinate, including the logarithmic offset. -/
theorem hasDerivAt_penaltyCoordinate {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    HasDerivAt penaltyCoordinate (-penaltyJacobian θ) θ := by
  have hi : 1 ≤ θ⁻¹ := (one_le_inv₀ hθ).2 hθ1
  have h3 : 0 < log 3 := log_pos (by norm_num)
  have hu : 0 < log 3 + θ⁻¹ := by positivity
  have hlu : 0 < log (log 3 + θ⁻¹) := log_pos (by linarith)
  have h := (((hasDerivAt_inv hθ.ne').const_add (log 3)).log hu.ne').sqrt hlu.ne'
  convert h using 1
  · rfl
  · dsimp only [penaltyJacobian, penaltyCoordinate]
    field_simp
    ring

/-- The original logarithmic measure is bounded by six times the new Jacobian. -/
theorem frequency_weight_le_jacobian {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    1 / (θ * sqrt (log (3 / θ))) ≤ 6 * penaltyJacobian θ := by
  have hs := penaltyCoordinate_pos hθ hθ1
  have hL := hs.trans_le (penaltyCoordinate_le hθ hθ1)
  have h3 : 0 < log 3 := log_pos (by norm_num)
  have hfactor : 1 + θ * log 3 ≤ 3 := by
    have := mul_le_mul_of_nonneg_right hθ1 h3.le
    linarith [log_three_lt_d9]
  have hsmall := penaltyCoordinate_le hθ hθ1
  unfold penaltyJacobian
  apply (div_le_iff₀ (mul_pos hθ hL)).2
  field_simp
  nlinarith [mul_le_mul hfactor hsmall hs.le (by norm_num : (0 : ℝ) ≤ 3)]

end BretecheTenenbaumMean
