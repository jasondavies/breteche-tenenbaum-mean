module

public import BretecheTenenbaumMean.DyadicGoodSets
public import BretecheTenenbaumMean.HighFrequencyPrimeBound

@[expose] public section

/-! # The two-frequency estimate on each dyadic good-set layer -/

namespace BretecheTenenbaumMean

open Real Finset PrimeSums

/-- A uniform comparison of the exact logarithmic envelope with `1/θ`. -/
theorem frequency_log_le {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    log (3 * exp θ⁻¹) ≤ 4 / θ := by
  rw [log_mul (by norm_num : (3 : ℝ) ≠ 0) (exp_ne_zero _), log_exp]
  have h3 := log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
  have hinv : 1 ≤ θ⁻¹ := (one_le_inv₀ hθ).2 hθ1
  rw [div_eq_mul_inv]
  linarith

/-- The envelope coefficient has the form used in the paper, with an explicit
constant absorbing `log (3 exp (1/θ))` rather than replacing it by an equality. -/
theorem frequency_sqrt_envelope_le {δ T θ φ : ℝ} (hT : 0 ≤ T)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hφ : 0 < φ) (hφ1 : φ ≤ 1) :
    sqrt (goodEnvelope δ T (exp φ⁻¹) * goodEnvelope δ T (exp θ⁻¹)) ≤
      4 * T * exp (-(penalty δ T (exp θ⁻¹) + penalty δ T (exp φ⁻¹)) / 2) /
        sqrt (θ * φ) := by
  let E := exp (-(penalty δ T (exp θ⁻¹) + penalty δ T (exp φ⁻¹)) / 2)
  have hE : 0 < E := exp_pos _
  have hsq : exp (-penalty δ T (exp φ⁻¹)) * exp (-penalty δ T (exp θ⁻¹)) = E ^ 2 := by
    dsimp only [E]
    rw [pow_two, ← exp_add, ← exp_add]
    congr 1
    ring
  have he : goodEnvelope δ T (exp φ⁻¹) * goodEnvelope δ T (exp θ⁻¹) =
      (T * E) ^ 2 * (log (3 * exp φ⁻¹) * log (3 * exp θ⁻¹)) := by
    unfold goodEnvelope
    calc _ = T ^ 2 * (exp (-penalty δ T (exp φ⁻¹)) * exp (-penalty δ T (exp θ⁻¹))) *
        (log (3 * exp φ⁻¹) * log (3 * exp θ⁻¹)) := by ring
      _ = _ := by rw [hsq]; ring
  have hLθ : 0 ≤ log (3 * exp θ⁻¹) := log_nonneg (by
    have := one_le_exp_iff.2 (inv_nonneg.2 hθ.le); linarith)
  have hL := mul_le_mul (frequency_log_le hφ hφ1) (frequency_log_le hθ hθ1)
    hLθ (by positivity : (0 : ℝ) ≤ 4 / φ)
  have hL' : log (3 * exp φ⁻¹) * log (3 * exp θ⁻¹) ≤ 16 / (θ * φ) := by
    convert hL using 1; ring
  have hs : sqrt (log (3 * exp φ⁻¹) * log (3 * exp θ⁻¹)) ≤ 4 / sqrt (θ * φ) := by
    have := sqrt_le_sqrt hL'
    rw [sqrt_div (by norm_num : (0 : ℝ) ≤ 16)] at this
    norm_num at this ⊢
    exact this
  rw [he, sqrt_mul (sq_nonneg _), sqrt_sq (mul_nonneg hT hE.le)]
  calc _ ≤ (T * E) * (4 / sqrt (θ * φ)) :=
      mul_le_mul_of_nonneg_left hs (mul_nonneg hT hE.le)
    _ = _ := by ring

/-- The positive analytic kernel left after good-set extraction. -/
noncomputable def highFrequencyKernel (x θ φ : ℝ) : ℝ :=
  (φ / θ) ^ sqrt 2 * (1 + θ * log x) *
    sqrt (φ * log x / (1 + (φ - θ) * log x)) /
    (sqrt (θ * φ) * φ ^ 2 * sqrt (log (3 / φ)) * log x)

theorem highFrequencyKernel_nonneg {x θ φ : ℝ} (hx : 1 ≤ x) (hθ : 0 ≤ θ)
    (hφ : 0 ≤ φ) : 0 ≤ highFrequencyKernel x θ φ := by
  have hl := log_nonneg hx
  unfold highFrequencyKernel
  positivity

end BretecheTenenbaumMean
