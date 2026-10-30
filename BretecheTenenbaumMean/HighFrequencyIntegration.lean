module

public import BretecheTenenbaumMean.HighFrequencyRegions
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! # Integration in the larger frequency -/

namespace BretecheTenenbaumMean

open Real MeasureTheory

/-- Continuity of the regularized kernel on the ordered frequency interval. -/
theorem continuousOn_regularizedHighKernel {ε θ b : ℝ}
    (hε : 0 < ε) (hθ : 0 < θ) (hb : b ≤ 1) :
    ContinuousOn (regularizedHighKernel ε θ) (Set.Icc θ b) := by
  intro φ hφ
  have hφ0 : 0 < φ := hθ.trans_le hφ.1
  have hd : 0 < φ - θ + ε := by linarith [hφ.1]
  have hlog : 0 < log (3 / φ) := log_pos ((lt_div_iff₀ hφ0).2 (by linarith [hφ.2]))
  apply ContinuousAt.continuousWithinAt
  unfold regularizedHighKernel
  fun_prop (disch := positivity)

/-- The inverse square root has its usual antiderivative, including endpoint zero. -/
theorem integral_inv_sqrt {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, (sqrt t)⁻¹) = 2 * (sqrt b - sqrt a) := by
  calc
    _ = ∫ t in a..b, t ^ (-1 / 2 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht0 : 0 ≤ t := ha.trans ((Set.uIcc_of_le hab ▸ ht).1)
      change (sqrt t)⁻¹ = t ^ (-1 / 2 : ℝ)
      rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, rpow_neg ht0, ← sqrt_eq_rpow]
    _ = _ := by
      rw [integral_rpow (Or.inl (by norm_num))]
      norm_num
      rw [← sqrt_eq_rpow, ← sqrt_eq_rpow]
      ring

/-- Uniform integral bound for the regularized diagonal singularity. -/
theorem integral_shifted_inv_sqrt_le {ε θ b : ℝ} (hε : 0 ≤ ε) (hθb : θ ≤ b) :
    (∫ φ in θ..b, (sqrt (φ - θ + ε))⁻¹) ≤ 2 * sqrt (b - θ) := by
  have he : (fun φ : ℝ ↦ (sqrt (φ - θ + ε))⁻¹) =
      (fun φ : ℝ ↦ (sqrt (φ + (ε - θ)))⁻¹) := by
    funext φ
    congr 2
    ring
  rw [he, intervalIntegral.integral_comp_add_right (fun t : ℝ ↦ (sqrt t)⁻¹) (ε - θ)]
  rw [show θ + (ε - θ) = ε by ring, show b + (ε - θ) = b - θ + ε by ring]
  rw [integral_inv_sqrt hε (by linarith)]
  have hd : 0 ≤ b - θ := sub_nonneg.2 hθb
  have hs : sqrt (b - θ + ε) ≤ sqrt (b - θ) + sqrt ε := by
    apply (sqrt_le_left (by positivity)).2
    rw [add_sq, sq_sqrt hd, sq_sqrt hε]
    nlinarith [mul_nonneg (sqrt_nonneg (b - θ)) (sqrt_nonneg ε)]
  linarith

/-- The inverse square-root majorant is integrable for a positive regularizer. -/
theorem intervalIntegrable_shifted_inv_sqrt {ε θ b : ℝ} (hε : 0 < ε) (hθb : θ ≤ b) :
    IntervalIntegrable (fun φ ↦ (sqrt (φ - θ + ε))⁻¹) volume θ b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hθb]
  intro φ hφ
  have hd : 0 < φ - θ + ε := by linarith [hφ.1]
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := positivity)

/-- Integrating the near-diagonal majorant costs a universal constant. -/
theorem integral_regularizedHighKernel_near {ε θ b : ℝ}
    (hε : 0 < ε) (hεθ : ε ≤ θ) (hθ : 0 < θ)
    (hθb : θ ≤ b) (hb2 : b ≤ 2 * θ) (hb1 : b ≤ 1) :
    (∫ φ in θ..b, regularizedHighKernel ε θ φ) ≤
      48 / (θ * sqrt (log (3 / θ))) := by
  have hlog : 0 < log (3 / θ) := log_pos ((lt_div_iff₀ hθ).2 (by linarith))
  have hcont := continuousOn_regularizedHighKernel hε hθ hb1
  have hi : IntervalIntegrable (regularizedHighKernel ε θ) volume θ b :=
    hcont.intervalIntegrable_of_Icc hθb
  let A := 24 / (θ * sqrt θ * sqrt (log (3 / θ)))
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hmono := intervalIntegral.integral_mono_on hθb hi
    ((intervalIntegrable_shifted_inv_sqrt hε hθb).const_mul A)
    (fun φ hφ ↦ regularizedHighKernel_near hε hεθ hθ hφ.1 (hφ.2.trans hb2) (hφ.2.trans hb1))
  rw [intervalIntegral.integral_const_mul] at hmono
  calc _ ≤ A * (∫ φ in θ..b, (sqrt (φ - θ + ε))⁻¹) := hmono
    _ ≤ A * (2 * sqrt (b - θ)) :=
      mul_le_mul_of_nonneg_left (integral_shifted_inv_sqrt_le hε.le hθb) hA
    _ ≤ A * (2 * sqrt θ) := by gcongr; linarith
    _ = _ := by dsimp only [A]; field_simp; norm_num

/-- The power tail away from zero is uniformly bounded by its lower endpoint. -/
theorem integral_power_tail_le {θ a b : ℝ} (hθ : 0 < θ) (hθa : θ ≤ a) (hab : a ≤ b) :
    (∫ φ in a..b, φ ^ (-65 / 64 : ℝ)) ≤ 64 * θ ^ (-1 / 64 : ℝ) := by
  have ha : 0 < a := hθ.trans_le hθa
  have hb : 0 < b := ha.trans_le hab
  have hzero : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    intro h
    linarith [h.1]
  rw [integral_rpow (Or.inr ⟨by norm_num, hzero⟩)]
  norm_num
  have hpow := rpow_le_rpow_of_nonpos hθ hθa (show (-1 / 64 : ℝ) ≤ 0 by norm_num)
  have hp := (rpow_pos_of_pos hb (-1 / 64 : ℝ)).le
  nlinarith

/-- Integration of the far-diagonal majorant. -/
theorem integral_regularizedHighKernel_far {ε θ a b : ℝ}
    (hε : 0 < ε) (hεθ : ε ≤ θ) (hθ : 0 < θ)
    (hθa : 2 * θ ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    (∫ φ in a..b, regularizedHighKernel ε θ φ) ≤
      768 / (θ * sqrt (log (3 / θ))) := by
  have hθa' : θ ≤ a := by linarith
  have ha : 0 < a := hθ.trans_le hθa'
  have hlog : 0 < log (3 / θ) := log_pos ((lt_div_iff₀ hθ).2 (by linarith))
  have hi : IntervalIntegrable (regularizedHighKernel ε θ) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact (continuousOn_regularizedHighKernel hε hθ hb1).mono
      (Set.Icc_subset_Icc hθa' le_rfl)
  have hp : IntervalIntegrable (fun φ : ℝ ↦ φ ^ (-65 / 64 : ℝ)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    apply continuousOn_id.rpow_const
    intro φ hφ
    exact Or.inl (ha.trans_le hφ.1).ne'
  let A := 12 * θ ^ (-63 / 64 : ℝ) / sqrt (log (3 / θ))
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hmono := intervalIntegral.integral_mono_on hab hi (hp.const_mul A)
    (fun φ hφ ↦ regularizedHighKernel_far hε hεθ hθ (hθa.trans hφ.1) (hφ.2.trans hb1))
  rw [intervalIntegral.integral_const_mul] at hmono
  calc _ ≤ A * (∫ φ in a..b, φ ^ (-65 / 64 : ℝ)) := hmono
    _ ≤ A * (64 * θ ^ (-1 / 64 : ℝ)) :=
      mul_le_mul_of_nonneg_left (integral_power_tail_le hθ hθa' hab) hA
    _ = _ := by
      dsimp only [A]
      have he : θ ^ (-63 / 64 : ℝ) * θ ^ (-1 / 64 : ℝ) = θ⁻¹ := by
        rw [← rpow_add hθ]
        norm_num [rpow_neg_one]
      calc _ = 768 * (θ ^ (-63 / 64 : ℝ) * θ ^ (-1 / 64 : ℝ)) / sqrt (log (3 / θ)) := by ring
        _ = _ := by rw [he]; ring

/-- The full integral in the larger frequency, uniformly in the diagonal regularizer. -/
theorem integral_regularizedHighKernel_le {ε θ : ℝ}
    (hε : 0 < ε) (hεθ : ε ≤ θ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    (∫ φ in θ..1, regularizedHighKernel ε θ φ) ≤
      816 / (θ * sqrt (log (3 / θ))) := by
  have hden : 0 < θ * sqrt (log (3 / θ)) :=
    mul_pos hθ (sqrt_pos.2 (log_pos ((lt_div_iff₀ hθ).2 (by linarith))))
  by_cases h2 : 2 * θ ≤ 1
  · have hθ2 : θ ≤ 2 * θ := by linarith
    have hcont := continuousOn_regularizedHighKernel hε hθ (b := 1) le_rfl
    have hi : IntervalIntegrable (regularizedHighKernel ε θ) volume θ (2 * θ) :=
      (hcont.mono (Set.Icc_subset_Icc le_rfl h2)).intervalIntegrable_of_Icc hθ2
    have hi' : IntervalIntegrable (regularizedHighKernel ε θ) volume (2 * θ) 1 :=
      (hcont.mono (Set.Icc_subset_Icc hθ2 le_rfl)).intervalIntegrable_of_Icc h2
    rw [← intervalIntegral.integral_add_adjacent_intervals hi hi']
    have hn := integral_regularizedHighKernel_near hε hεθ hθ hθ2 le_rfl h2
    have hf := integral_regularizedHighKernel_far hε hεθ hθ le_rfl h2 (by norm_num : (1 : ℝ) ≤ 1)
    calc _ ≤ 48 / (θ * sqrt (log (3 / θ))) + 768 / (θ * sqrt (log (3 / θ))) := add_le_add hn hf
      _ = _ := by ring
  · exact (integral_regularizedHighKernel_near hε hεθ hθ hθ1 (le_of_not_ge h2) le_rfl).trans
      (div_le_div_of_nonneg_right (by norm_num) hden.le)

end BretecheTenenbaumMean
