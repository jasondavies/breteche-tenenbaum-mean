module

public import BretecheTenenbaumMean.PenaltyGaussian

@[expose] public section

/-! # The uniform penalty integral in the high-frequency argument -/

namespace BretecheTenenbaumMean

open Real MeasureTheory

noncomputable def penaltyGaussian (δ T s : ℝ) : ℝ :=
  exp (-(δ / 2) * s ^ 2) +
    exp (-(δ * criticalSlope / 2) * (s - sqrt (criticalSlope * log T)) ^ 2)

theorem penaltyGaussian_nonneg (δ T s : ℝ) : 0 ≤ penaltyGaussian δ T s := by
  unfold penaltyGaussian
  positivity

theorem continuous_penaltyGaussian (δ T : ℝ) : Continuous (penaltyGaussian δ T) := by
  unfold penaltyGaussian
  fun_prop

/-- The coordinate reverses the order of the frequencies. -/
theorem penaltyCoordinate_antitone {θ φ : ℝ} (hθ : 0 < θ) (hθφ : θ ≤ φ) :
    penaltyCoordinate φ ≤ penaltyCoordinate θ := by
  have hφ : 0 < φ := hθ.trans_le hθφ
  have h3 : 0 < log 3 := log_pos (by norm_num)
  apply sqrt_le_sqrt
  exact log_le_log (by positivity) (add_le_add le_rfl (inv_anti₀ hθ hθφ))

theorem continuousOn_penaltyJacobian {a : ℝ} (ha : 0 < a) :
    ContinuousOn penaltyJacobian (Set.Icc a 1) := by
  intro θ hθ
  have hθ0 : 0 < θ := ha.trans_le hθ.1
  have hs := penaltyCoordinate_pos hθ0 hθ.2
  have h3 : 0 < log 3 := log_pos (by norm_num)
  have hu : 0 < log 3 + θ⁻¹ := by positivity
  have hi : 1 ≤ θ⁻¹ := (one_le_inv₀ hθ0).2 hθ.2
  have hlu : 0 < log (log 3 + θ⁻¹) := log_pos (by linarith)
  apply ContinuousAt.continuousWithinAt
  unfold penaltyJacobian penaltyCoordinate
  fun_prop (disch := positivity)

/-- Substitution with the positive Jacobian and reversed endpoints. -/
theorem integral_penalty_substitution {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ θ in a..1, g (penaltyCoordinate θ) * penaltyJacobian θ) =
      ∫ s in penaltyCoordinate 1..penaltyCoordinate a, g s := by
  have hder : ∀ θ ∈ Set.uIcc a 1, HasDerivAt penaltyCoordinate (-penaltyJacobian θ) θ := by
    rw [Set.uIcc_of_le ha1]
    intro θ hθ
    exact hasDerivAt_penaltyCoordinate (ha.trans_le hθ.1) hθ.2
  have hc : ContinuousOn (fun θ ↦ -penaltyJacobian θ) (Set.uIcc a 1) := by
    rw [Set.uIcc_of_le ha1]
    exact (continuousOn_penaltyJacobian ha).neg
  have hsub := intervalIntegral.integral_comp_mul_deriv hder hc hg
  calc
    _ = -(∫ θ in a..1, g (penaltyCoordinate θ) * (-penaltyJacobian θ)) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only
      ring
    _ = -(∫ s in penaltyCoordinate a..penaltyCoordinate 1, g s) := by
      simpa only [Function.comp_def] using congrArg Neg.neg hsub
    _ = _ := (intervalIntegral.integral_symm _ _).symm

/-- Any translated Gaussian integral over an ordered interval is bounded by
the whole Gaussian integral. -/
theorem integral_translated_gaussian_le {k a b : ℝ} (hk : 0 < k) (hab : a ≤ b) (c : ℝ) :
    (∫ s in a..b, exp (-k * (s - c) ^ 2)) ≤ sqrt (π / k) := by
  rw [intervalIntegral.integral_comp_sub_right (fun s : ℝ ↦ exp (-k * s ^ 2)) c]
  rw [intervalIntegral.integral_of_le (sub_le_sub_right hab c)]
  calc _ ≤ ∫ s : ℝ, exp (-k * s ^ 2) :=
      setIntegral_le_integral (integrable_exp_neg_mul_sq hk) (Filter.Eventually.of_forall (fun _ ↦ (exp_pos _).le))
    _ = _ := integral_gaussian k

/-- The Gaussian majorant has uniformly bounded mass, regardless of the center. -/
theorem integral_penaltyGaussian_le {δ a b : ℝ} (hδ : 0 < δ) (hab : a ≤ b) (T : ℝ) :
    (∫ s in a..b, penaltyGaussian δ T s) ≤
      sqrt (π / (δ / 2)) + sqrt (π / (δ * criticalSlope / 2)) := by
  have h1 : Continuous (fun s : ℝ ↦ exp (-(δ / 2) * s ^ 2)) := by fun_prop
  have h2 : Continuous (fun s : ℝ ↦ exp (-(δ * criticalSlope / 2) *
      (s - sqrt (criticalSlope * log T)) ^ 2)) := by fun_prop
  simp only [penaltyGaussian]
  rw [intervalIntegral.integral_add (h1.intervalIntegrable a b) (h2.intervalIntegrable a b)]
  have hfirst := integral_translated_gaussian_le (by positivity : 0 < δ / 2) hab (0 : ℝ)
  simp only [sub_zero] at hfirst
  exact add_le_add hfirst (integral_translated_gaussian_le
    (div_pos (mul_pos hδ criticalSlope_pos) (by norm_num)) hab _)

/-- The full penalty weight that remains after integrating in the larger frequency. -/
noncomputable def frequencyPenaltyWeight (δ T θ : ℝ) : ℝ :=
  exp (-penalty δ T (exp θ⁻¹) / 2) / (θ * sqrt (log (3 / θ)))

theorem frequencyPenaltyWeight_le {δ T θ : ℝ}
    (hδ : 0 ≤ δ) (hT : 1 < T) (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    frequencyPenaltyWeight δ T θ ≤
      6 * (penaltyGaussian δ T (penaltyCoordinate θ) * penaltyJacobian θ) := by
  have h := mul_le_mul (frequency_penalty_le_gaussians hδ hT hθ hθ1)
    (frequency_weight_le_jacobian hθ hθ1)
    (by positivity : 0 ≤ 1 / (θ * sqrt (log (3 / θ))))
    (penaltyGaussian_nonneg δ T (penaltyCoordinate θ))
  unfold frequencyPenaltyWeight
  change exp (-penalty δ T (exp θ⁻¹) / 2) * (1 / (θ * sqrt (log (3 / θ)))) ≤
    penaltyGaussian δ T (penaltyCoordinate θ) * (6 * penaltyJacobian θ) at h
  convert h using 1 <;> ring

theorem continuousOn_frequencyPenaltyWeight {δ T a : ℝ} (hT : 1 < T) (ha : 0 < a) :
    ContinuousOn (frequencyPenaltyWeight δ T) (Set.Icc a 1) := by
  intro θ hθ
  have hθ0 : 0 < θ := ha.trans_le hθ.1
  have hT0 : 0 < T := by linarith
  have hexp : 1 ≤ exp θ⁻¹ := one_le_exp_iff.2 (inv_nonneg.2 hθ0.le)
  have hL : 0 < log (3 * exp θ⁻¹) := log_pos (by linarith)
  have hlog : 0 < log (3 / θ) := log_pos ((lt_div_iff₀ hθ0).2 (by linarith [hθ.2]))
  apply ContinuousAt.continuousWithinAt
  unfold frequencyPenaltyWeight penalty
  fun_prop (disch := positivity)

/-- The remaining penalty integral is bounded independently of `T` and its
positive lower endpoint. Both branches of the exact penalty are included. -/
theorem frequency_penalty_integral_le {δ T a : ℝ}
    (hδ : 0 < δ) (hT : 1 < T) (ha : 0 < a) (ha1 : a ≤ 1) :
    (∫ θ in a..1, frequencyPenaltyWeight δ T θ) ≤
      6 * (sqrt (π / (δ / 2)) + sqrt (π / (δ * criticalSlope / 2))) := by
  have hf : IntervalIntegrable (frequencyPenaltyWeight δ T) volume a 1 :=
    (continuousOn_frequencyPenaltyWeight hT ha).intervalIntegrable_of_Icc ha1
  have hs : ContinuousOn penaltyCoordinate (Set.Icc a 1) := by
    intro θ hθ
    exact (hasDerivAt_penaltyCoordinate (ha.trans_le hθ.1) hθ.2).continuousAt.continuousWithinAt
  have hg : IntervalIntegrable (fun θ ↦ penaltyGaussian δ T (penaltyCoordinate θ) * penaltyJacobian θ)
      volume a 1 := ((continuous_penaltyGaussian δ T).comp_continuousOn hs |>.mul
        (continuousOn_penaltyJacobian ha)).intervalIntegrable_of_Icc ha1
  have hm := intervalIntegral.integral_mono_on ha1 hf (hg.const_mul 6)
    (fun θ hθ ↦ frequencyPenaltyWeight_le hδ.le hT (ha.trans_le hθ.1) hθ.2)
  rw [intervalIntegral.integral_const_mul, integral_penalty_substitution ha ha1 (continuous_penaltyGaussian δ T)] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left (integral_penaltyGaussian_le hδ
    (penaltyCoordinate_antitone ha ha1) T) (by norm_num))

end BretecheTenenbaumMean
