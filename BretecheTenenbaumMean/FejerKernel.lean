module

public import Mathlib

@[expose] public section

/-! # A compact-frequency kernel for the second moment

The triangular weight on `[0,1]` has a nonnegative cosine transform. It
dominates a constant multiple of the unit triangular kernel in physical space.
-/

namespace BretecheTenenbaumMean

open Real MeasureTheory

noncomputable def fejerKernel (t : ℝ) : ℝ :=
  if t = 0 then 1 / 2 else (1 - cos t) / t ^ 2

theorem fejerKernel_nonneg (t : ℝ) : 0 ≤ fejerKernel t := by
  unfold fejerKernel
  split_ifs
  · norm_num
  · exact div_nonneg (sub_nonneg.mpr (cos_le_one t)) (sq_nonneg _)

theorem integral_triangular_cos (t : ℝ) :
    (∫ θ in (0 : ℝ)..1, (1 - θ) * cos (θ * t)) = fejerKernel t := by
  by_cases ht : t = 0
  · subst t
    simp only [mul_zero, cos_zero, mul_one, fejerKernel, ↓reduceIte]
    rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ)) (g := fun θ : ℝ => θ)
      (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _)]
    norm_num
  let F : ℝ → ℝ := fun θ => (1 - θ) * sin (θ * t) / t - cos (θ * t) / t ^ 2
  have hderiv (θ : ℝ) : HasDerivAt F ((1 - θ) * cos (θ * t)) θ := by
    have harg : HasDerivAt (fun u : ℝ => u * t) t θ := by
      simpa using (hasDerivAt_id θ).mul_const t
    have h := (((hasDerivAt_const θ (1 : ℝ)).sub (hasDerivAt_id θ)).mul harg.sin).div_const t
    have h' := h.sub (harg.cos.div_const (t ^ 2))
    convert h' using 1
    · rfl
    · simp only [Pi.sub_apply, id_eq]
      field_simp
      ring
  have hi : IntervalIntegrable (fun θ : ℝ => (1 - θ) * cos (θ * t)) volume 0 1 :=
    (by fun_prop : Continuous (fun θ : ℝ => (1 - θ) * cos (θ * t))).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hderiv θ) hi]
  simp [F, fejerKernel, ht]
  ring

theorem triangle_le_fejerKernel (t : ℝ) :
    max (1 - |t|) 0 ≤ (π ^ 2 / 2) * fejerKernel t := by
  have hπ : 0 < π := Real.pi_pos
  by_cases ht : t = 0
  · subst t
    simp only [abs_zero, sub_zero, max_eq_left zero_le_one, fejerKernel, ↓reduceIte]
    nlinarith [Real.pi_gt_three]
  by_cases ha : |t| ≤ 1
  · have hcos := Real.cos_le_one_sub_mul_cos_sq (ha.trans (by linarith [Real.pi_gt_three]))
    have htsq : 0 < t ^ 2 := sq_pos_of_ne_zero ht
    have hK : 2 / π ^ 2 ≤ fejerKernel t := by
      rw [fejerKernel, ite_eq_right ht, le_div_iff₀ htsq]
      linarith
    have hm := mul_le_mul_of_nonneg_left hK (show 0 ≤ π ^ 2 / 2 by positivity)
    have hcancel : (π ^ 2 / 2) * (2 / π ^ 2) = 1 := by field_simp
    rw [hcancel] at hm
    exact (max_le (by linarith [abs_nonneg t]) zero_le_one).trans hm
  · rw [max_eq_right (by linarith : 1 - |t| ≤ 0)]
    exact mul_nonneg (by positivity) (fejerKernel_nonneg t)

end BretecheTenenbaumMean
