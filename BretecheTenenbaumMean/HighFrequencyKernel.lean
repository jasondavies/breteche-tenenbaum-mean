module

public import BretecheTenenbaumMean.HighFrequencyDyadic
public import BretecheTenenbaumMean.Penalty

@[expose] public section

/-! # The regularized high-frequency kernel -/

namespace BretecheTenenbaumMean

open Real

/-- The parameter `ε = 1/log x` resolves the diagonal singularity. -/
noncomputable def regularizedHighKernel (ε θ φ : ℝ) : ℝ :=
  (φ / θ) ^ sqrt 2 * (θ + ε) /
    (sqrt θ * φ ^ 2 * sqrt (φ - θ + ε) * sqrt (log (3 / φ)))

/-- Exact cancellation of the square-root prime-sum factors. -/
theorem highFrequencyKernel_eq_regularized {x θ φ : ℝ}
    (hx : 1 < x) (hθ : 0 < θ) (hθφ : θ ≤ φ) :
    highFrequencyKernel x θ φ = regularizedHighKernel (log x)⁻¹ θ φ := by
  have hl : 0 < log x := log_pos hx
  have hφ : 0 < φ := hθ.trans_le hθφ
  have hd : 0 < φ - θ + (log x)⁻¹ :=
    add_pos_of_nonneg_of_pos (sub_nonneg.2 hθφ) (inv_pos.2 hl)
  have hd' : 0 < 1 + (φ - θ) * log x := by
    have : 0 ≤ φ - θ := sub_nonneg.2 hθφ
    positivity
  have hratio : φ * log x / (1 + (φ - θ) * log x) =
      φ / (φ - θ + (log x)⁻¹) := by
    field_simp
    ring
  unfold highFrequencyKernel regularizedHighKernel
  rw [hratio, sqrt_div hφ.le, sqrt_mul hθ.le]
  have hsφ : sqrt φ ≠ 0 := (sqrt_pos.2 hφ).ne'
  field_simp
  ring

/-- The high-frequency hypothesis is precisely the bound on the regularizer. -/
theorem inv_log_le_frequency {x θ : ℝ} (hθ : 0 < θ) (hx : exp θ⁻¹ ≤ x) :
    0 < (log x)⁻¹ ∧ (log x)⁻¹ ≤ θ := by
  have hl : θ⁻¹ ≤ log x := (le_log_iff_exp_le (lt_of_lt_of_le (exp_pos _) hx)).2 hx
  have hl0 : 0 < log x := (inv_pos.2 hθ).trans_le hl
  refine ⟨inv_pos.2 hl0, ?_⟩
  have h := inv_anti₀ (inv_pos.2 hθ) hl
  simpa only [inv_inv] using h

/-- The penalty is nonnegative on its intended parameter range. -/
theorem penalty_nonneg {δ T y : ℝ} (hδ : 0 ≤ δ) (hT : 1 ≤ T) (hy : 1 ≤ y) :
    0 ≤ penalty δ T y := by
  have hlog3 : 1 ≤ log 3 := by linarith [log_three_gt_d9]
  have hLy : 1 ≤ log (3 * y) := hlog3.trans (log_le_log (by norm_num) (by linarith))
  have hT0 : 0 ≤ T := by linarith
  have hprod : 1 ≤ T * log (3 * y) := by nlinarith
  unfold penalty
  exact mul_nonneg hδ (le_min (log_nonneg hprod)
    (div_nonneg (sq_nonneg _) (log_nonneg hT)))

end BretecheTenenbaumMean
